/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Composition-Product of a measure and a kernel

This operation, denoted by `⊗ₘ`, takes `μ : Measure α` and `κ : Kernel α β` and creates
`μ ⊗ₘ κ : Measure (α × β)`. The integral of a function against `μ ⊗ₘ κ` is
`∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ`.

`μ ⊗ₘ κ` is defined as `((Kernel.const Unit μ) ⊗ₖ (Kernel.prodMkLeft Unit κ)) ()`.

## Main definitions

* `Measure.compProd`: from `μ : Measure α` and `κ : Kernel α β`, get a `Measure (α × β)`.

## Notation

* `μ ⊗ₘ κ = μ.compProd κ`
-/

@[expose] public section

open scoped ENNReal

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- The composition-product of a measure and a kernel. -/
noncomputable
/--
Definition of `compProd` / `compProd` 的定义

English:
definition compProd
  signature: (μ : Measure α) (κ : Kernel α β)
  body: (Kernel.const Unit μ otimesₖ Kernel.prodMkLeft Unit κ) ()

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " otimesₘ " => MeasureTheory.Measure.compProd

@[simp]

中文:
定义 compProd
  签名: (μ : Measure α) (κ : Kernel α β)
  定义体: (Kernel.const Unit μ otimesₖ Kernel.prodMkLeft Unit κ) ()

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " otimesₘ " => MeasureTheory.Measure.compProd

@[simp]

Depends on / 依赖: Kernel, Kernel.const, Kernel.prodMkLeft, prodMkLeft
-/
def compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β) :=
  (Kernel.const Unit μ otimesₖ Kernel.prodMkLeft Unit κ) ()

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " otimesₘ " => MeasureTheory.Measure.compProd

@[simp]
/--
lemma `compProd_of_not_sfinite` / 引理 `compProd_of_not_sfinite`

English:
lemma compProd_of_not_sfinite
  given: (μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ)
  proof: by
  rw [compProd]; rw [Kernel.compProd_of_not_isSFiniteKernel_left]; rw [zero_apply]
  rwa [Kernel.isSFiniteKernel_const]

@[simp]

中文:
引理 compProd_of_not_sfinite
  条件: (μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ)
  证明: by
  rw [compProd]; rw [Kernel.compProd_of_not_isSFiniteKernel_left]; rw [zero_apply]
  rwa [Kernel.isSFiniteKernel_const]

@[simp]

Depends on / 依赖: Kernel, Kernel.compProd_of_not_isSFiniteKernel_left, Kernel.isSFiniteKernel_const, compProd, compProd_of_not_isSFiniteKernel_left, isSFiniteKernel_const, zero_apply
-/
lemma compProd_of_not_sfinite (μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) :
    μ otimesₘ κ = 0 := by
  rw [compProd]; rw [Kernel.compProd_of_not_isSFiniteKernel_left]; rw [zero_apply]
  rwa [Kernel.isSFiniteKernel_const]

@[simp]
/--
lemma `compProd_of_not_isSFiniteKernel` / 引理 `compProd_of_not_isSFiniteKernel`

English:
lemma compProd_of_not_isSFiniteKernel
  given: (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ)
  proof: by
  rw [compProd]; rw [Kernel.compProd_of_not_isSFiniteKernel_right]; rw [zero_apply]
  rwa [Kernel.isSFiniteKernel_prodMkLeft_unit]

中文:
引理 compProd_of_not_isSFiniteKernel
  条件: (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ)
  证明: by
  rw [compProd]; rw [Kernel.compProd_of_not_isSFiniteKernel_right]; rw [zero_apply]
  rwa [Kernel.isSFiniteKernel_prodMkLeft_unit]

Depends on / 依赖: Kernel, Kernel.compProd_of_not_isSFiniteKernel_right, Kernel.isSFiniteKernel_prodMkLeft_unit, compProd, compProd_of_not_isSFiniteKernel_right, isSFiniteKernel_prodMkLeft_unit, zero_apply
-/
lemma compProd_of_not_isSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) :
    μ otimesₘ κ = 0 := by
  rw [compProd]; rw [Kernel.compProd_of_not_isSFiniteKernel_right]; rw [zero_apply]
  rwa [Kernel.isSFiniteKernel_prodMkLeft_unit]

/--
lemma `compProd_apply` / 引理 `compProd_apply`

English:
lemma compProd_apply
  given: [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s)
  proof: by
  simp_rw [compProd, Kernel.compProd_apply hs, Kernel.const_apply, Kernel.prodMkLeft_apply']

@[simp]

中文:
引理 compProd_apply
  条件: [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s)
  证明: by
  simp_rw [compProd, Kernel.compProd_apply hs, Kernel.const_apply, Kernel.prodMkLeft_apply']

@[simp]

Depends on / 依赖: Kernel, Kernel.compProd_apply, Kernel.const_apply, Kernel.prodMkLeft_apply, compProd, compProd_apply, const_apply, prodMkLeft_apply, simp_rw
-/
lemma compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ otimesₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ := by
  simp_rw [compProd, Kernel.compProd_apply hs, Kernel.const_apply, Kernel.prodMkLeft_apply']

@[simp]
/--
lemma `compProd_apply_univ` / 引理 `compProd_apply_univ`

English:
lemma compProd_apply_univ
  given: [SFinite μ] [IsMarkovKernel κ]
  statement: (μ otimesₘ κ) univ = μ univ
  proof: by
  simp [compProd]

中文:
引理 compProd_apply_univ
  条件: [SFinite μ] [IsMarkovKernel κ]
  结论: (μ otimesₘ κ) univ = μ univ
  证明: by
  simp [compProd]

Depends on / 依赖: compProd
-/
lemma compProd_apply_univ [SFinite μ] [IsMarkovKernel κ] : (μ otimesₘ κ) univ = μ univ := by
  simp [compProd]

/--
lemma `compProd_apply_prod` / 引理 `compProd_apply_prod`

English:
lemma compProd_apply_prod
  statement: [SFinite μ] [IsSFiniteKernel κ]
  proof: by
  simp [compProd, Kernel.compProd_apply_prod hs ht]

中文:
引理 compProd_apply_prod
  结论: [SFinite μ] [IsSFiniteKernel κ]
  证明: by
  simp [compProd, Kernel.compProd_apply_prod hs ht]

Depends on / 依赖: Kernel, Kernel.compProd_apply_prod, compProd, compProd_apply_prod
-/
lemma compProd_apply_prod [SFinite μ] [IsSFiniteKernel κ]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ otimesₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ := by
  simp [compProd, Kernel.compProd_apply_prod hs ht]

/--
lemma `compProd_congr` / 引理 `compProd_congr`

English:
lemma compProd_congr
  given: [IsSFiniteKernel κ] [IsSFiniteKernel η] (h : κ =ᵐ[μ] η)
  proof: by
  rw [compProd]; rw [compProd]
  congr 1
  refine Kernel.compProd_congr ?_
  simpa

中文:
引理 compProd_congr
  条件: [IsSFiniteKernel κ] [IsSFiniteKernel η] (h : κ =ᵐ[μ] η)
  证明: by
  rw [compProd]; rw [compProd]
  congr 1
  refine Kernel.compProd_congr ?_
  simpa

Depends on / 依赖: Kernel, Kernel.compProd_congr, compProd, compProd_congr
-/
lemma compProd_congr [IsSFiniteKernel κ] [IsSFiniteKernel η] (h : κ =ᵐ[μ] η) :
    μ otimesₘ κ = μ otimesₘ η := by
  rw [compProd]; rw [compProd]
  congr 1
  refine Kernel.compProd_congr ?_
  simpa

/--
lemma `compProd_zero_left` / 引理 `compProd_zero_left`

English:
lemma compProd_zero_left
  given: (κ : Kernel α β)
  statement: (0 : Measure α) otimesₘ κ = 0
  proof: by simp [compProd]

中文:
引理 compProd_zero_left
  条件: (κ : Kernel α β)
  结论: (0 : Measure α) otimesₘ κ = 0
  证明: by simp [compProd]
-/
@[simp] lemma compProd_zero_left (κ : Kernel α β) : (0 : Measure α) otimesₘ κ = 0 := by simp [compProd]

/--
lemma `compProd_zero_right` / 引理 `compProd_zero_right`

English:
lemma compProd_zero_right
  given: (μ : Measure α)
  statement: μ otimesₘ (0 : Kernel α β) = 0
  proof: by simp [compProd]

中文:
引理 compProd_zero_right
  条件: (μ : Measure α)
  结论: μ otimesₘ (0 : Kernel α β) = 0
  证明: by simp [compProd]
-/
@[simp] lemma compProd_zero_right (μ : Measure α) : μ otimesₘ (0 : Kernel α β) = 0 := by simp [compProd]

/--
lemma `compProd_eq_zero_iff` / 引理 `compProd_eq_zero_iff`

English:
lemma compProd_eq_zero_iff
  given: [SFinite μ] [IsSFiniteKernel κ]
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp_rw [← measure_univ_eq_zero]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ .univ)).mp ?_
    rw [← setLIntegral_univ]; rw [← compProd_apply_prod .univ .univ]; rw [h]
    simp
  · rw [← compProd_zero_right μ]
    exact compProd_congr h

中文:
引理 compProd_eq_zero_iff
  条件: [SFinite μ] [IsSFiniteKernel κ]
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp_rw [← measure_univ_eq_zero]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ .univ)).mp ?_
    rw [← setLIntegral_univ]; rw [← compProd_apply_prod .univ .univ]; rw [h]
    simp
  · rw [← compProd_zero_right μ]
    exact compProd_congr h

Depends on / 依赖: Kernel, Kernel.measurable_coe, compProd_apply_prod, compProd_congr, compProd_zero_right, lintegral_eq_zero_iff, measurable_coe, measure_univ_eq_zero, setLIntegral_univ, simp_rw
-/
lemma compProd_eq_zero_iff [SFinite μ] [IsSFiniteKernel κ] :
    μ otimesₘ κ = 0 ↔ forallᵐ a ∂μ, κ a = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp_rw [← measure_univ_eq_zero]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ .univ)).mp ?_
    rw [← setLIntegral_univ]; rw [← compProd_apply_prod .univ .univ]; rw [h]
    simp
  · rw [← compProd_zero_right μ]
    exact compProd_congr h

/--
lemma `_root_.ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR` / 引理 `_root_.ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR`

English:
lemma _root_.ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR
  statement: {γ : Type*}
  proof: by
  ext s hs
  simp_rw [Kernel.compProd_apply hs, compProd_apply hs, Kernel.sectR_apply]

中文:
引理 _root_.ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR
  结论: {γ : 类型}
  证明: by
  ext s hs
  simp_rw [Kernel.compProd_apply hs, compProd_apply hs, Kernel.sectR_apply]

Depends on / 依赖: Kernel, Kernel.compProd_apply, Kernel.sectR_apply, compProd_apply, sectR_apply, simp_rw
-/
lemma _root_.ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR {γ : Type*}
    {mγ : MeasurableSpace γ} (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (a : α) :
    (κ otimesₖ η) a = (κ a) otimesₘ (Kernel.sectR η a) := by
  ext s hs
  simp_rw [Kernel.compProd_apply hs, compProd_apply hs, Kernel.sectR_apply]

/--
lemma `compProd_id` / 引理 `compProd_id`

English:
lemma compProd_id
  given: [SFinite μ]
  statement: μ otimesₘ Kernel.id = μ.map Function.diag
  proof: by
  ext s hs
  rw [compProd_apply hs]; rw [map_apply (measurable_id.prod measurable_id) hs]
  have h_meas a : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  simp_rw [Kernel.id_apply, dirac_apply' _ (h_meas _)]
  calc ∫⁻ a, (Prod.mk a ⁻¹' s).indicator 1 a ∂μ
  _ = ∫⁻ a, (Function.dia

中文:
引理 compProd_id
  条件: [SFinite μ]
  结论: μ otimesₘ Kernel.id = μ.map Function.diag
  证明: by
  ext s hs
  rw [compProd_apply hs]; rw [map_apply (measurable_id.prod measurable_id) hs]
  have h_meas a : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  simp_rw [Kernel.id_apply, dirac_apply' _ (h_meas _)]
  calc ∫⁻ a, (Prod.mk a ⁻¹' s).indicator 1 a ∂μ
  _ = ∫⁻ a, (Function.dia

Depends on / 依赖: Function, Function.diag, Kernel, Kernel.id_apply, MeasurableSet, MvPowerSeries, MvPowerSeries.isRestricted.add, Prod.mk, compProd_apply, dirac_apply, h_meas, id_apply, indicator, isRestricted, lintegral_indicator_one, map_apply, measurable_id, measurable_id.prod, measurable_prodMk_left, simp_rw
-/
lemma compProd_id [SFinite μ] : μ otimesₘ Kernel.id = μ.map Function.diag := by
  ext s hs
  rw [compProd_apply hs]; rw [map_apply (measurable_id.prod measurable_id) hs]
  have h_meas a : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  simp_rw [Kernel.id_apply, dirac_apply' _ (h_meas _)]
  calc ∫⁻ a, (Prod.mk a ⁻¹' s).indicator 1 a ∂μ
  _ = ∫⁻ a, (Function.diag ⁻¹' s).indicator 1 a ∂μ := rfl
  _ = μ (Function.diag ⁻¹' s) := by
    rw [lintegral_indicator_one]
    exact (measurable_id.prod measurable_id) hs

/--
lemma `ae_compProd_of_ae_ae` / 引理 `ae_compProd_of_ae_ae`

English:
lemma ae_compProd_of_ae_ae
  statement: {p : α × β -> Prop}
  proof: Kernel.ae_compProd_of_ae_ae hp h

中文:
引理 ae_compProd_of_ae_ae
  结论: {p : α × β -> 命题}
  证明: Kernel.ae_compProd_of_ae_ae hp h

Depends on / 依赖: Kernel, Kernel.ae_compProd_of_ae_ae, MvPowerSeries, MvPowerSeries.isRestricted.neg, ae_compProd_of_ae_ae, isRestricted
-/
lemma ae_compProd_of_ae_ae {p : α × β -> Prop}
    (hp : MeasurableSet {x | p x}) (h : forallᵐ a ∂μ, forallᵐ b ∂(κ a), p (a, b)) :
    forallᵐ x ∂(μ otimesₘ κ), p x :=
  Kernel.ae_compProd_of_ae_ae hp h

/--
lemma `ae_ae_of_ae_compProd` / 引理 `ae_ae_of_ae_compProd`

English:
lemma ae_ae_of_ae_compProd
  statement: [SFinite μ] [IsSFiniteKernel κ] {p : α × β -> Prop}
  proof: by
  convert! Kernel.ae_ae_of_ae_compProd h -- Much faster with `convert`

中文:
引理 ae_ae_of_ae_compProd
  结论: [SFinite μ] [IsSFiniteKernel κ] {p : α × β -> 命题}
  证明: by
  convert! Kernel.ae_ae_of_ae_compProd h -- Much faster with `convert`

Depends on / 依赖: Kernel, Kernel.ae_ae_of_ae_compProd, MvPowerSeries, MvPowerSeries.isRestricted.mul, ae_ae_of_ae_compProd, convert, faster, isRestricted
-/
lemma ae_ae_of_ae_compProd [SFinite μ] [IsSFiniteKernel κ] {p : α × β -> Prop}
    (h : forallᵐ x ∂(μ otimesₘ κ), p x) :
    forallᵐ a ∂μ, forallᵐ b ∂κ a, p (a, b) := by
  convert! Kernel.ae_ae_of_ae_compProd h -- Much faster with `convert`

/--
lemma `ae_compProd_iff` / 引理 `ae_compProd_iff`

English:
lemma ae_compProd_iff
  statement: [SFinite μ] [IsSFiniteKernel κ] {p : α × β -> Prop}
  proof: Kernel.ae_compProd_iff hp

中文:
引理 ae_compProd_iff
  结论: [SFinite μ] [IsSFiniteKernel κ] {p : α × β -> 命题}
  证明: Kernel.ae_compProd_iff hp

Depends on / 依赖: Kernel, Kernel.ae_compProd_iff, ae_compProd_iff
-/
lemma ae_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {p : α × β -> Prop}
    (hp : MeasurableSet {x | p x}) :
    (forallᵐ x ∂(μ otimesₘ κ), p x) ↔ forallᵐ a ∂μ, forallᵐ b ∂(κ a), p (a, b) :=
  Kernel.ae_compProd_iff hp

/--
lemma `ae_compProd_of_ae_fst` / 引理 `ae_compProd_of_ae_fst`

English:
lemma ae_compProd_of_ae_fst
  statement: (κ : Kernel α β) {p : α -> Prop} (hp : MeasurableSet {x | p x})
  proof: ae_compProd_of_ae_ae (measurable_fst hp) by filter_upwards [h] with a ha using by simp [ha]

中文:
引理 ae_compProd_of_ae_fst
  结论: (κ : Kernel α β) {p : α -> 命题} (hp : MeasurableSet {x | p x})
  证明: ae_compProd_of_ae_ae (measurable_fst hp) by filter_upwards [h] with a ha using by simp [ha]

Depends on / 依赖: ae_compProd_of_ae_ae, filter_upwards, measurable_fst
-/
lemma ae_compProd_of_ae_fst (κ : Kernel α β) {p : α -> Prop} (hp : MeasurableSet {x | p x})
    (h : forallᵐ a ∂μ, p a) :
    forallᵐ x ∂(μ otimesₘ κ), p x.1 :=
ae_compProd_of_ae_ae (measurable_fst hp) by filter_upwards [h] with a ha using by simp [ha]

/--
lemma `ae_eq_compProd_of_ae_eq_fst` / 引理 `ae_eq_compProd_of_ae_eq_fst`

English:
lemma ae_eq_compProd_of_ae_eq_fst
  statement: {γ : Type*} {mγ : MeasurableSpace γ} [MeasurableEq γ]
  proof: ae_compProd_of_ae_fst κ (measurableSet_eq_fun hf hg) h

中文:
引理 ae_eq_compProd_of_ae_eq_fst
  结论: {γ : 类型} {mγ : MeasurableSpace γ} [MeasurableEq γ]
  证明: ae_compProd_of_ae_fst κ (measurableSet_eq_fun hf hg) h

Depends on / 依赖: ae_compProd_of_ae_fst, measurableSet_eq_fun
-/
lemma ae_eq_compProd_of_ae_eq_fst {γ : Type*} {mγ : MeasurableSpace γ} [MeasurableEq γ]
    (κ : Kernel α β) {f g : α -> γ} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    (fun p => f p.1) =ᵐ[μ otimesₘ κ] (fun p => g p.1) :=
  ae_compProd_of_ae_fst κ (measurableSet_eq_fun hf hg) h

/-- The composition product of a measure and a constant kernel is the product between the two
measures. -/
@[simp]
/--
lemma `compProd_const` / 引理 `compProd_const`

English:
lemma compProd_const
  given: {ν : Measure β} [SFinite μ] [SFinite ν]
  proof: by
  ext s hs
  simp_rw [compProd_apply hs, prod_apply hs, Kernel.const_apply]

中文:
引理 compProd_const
  条件: {ν : Measure β} [SFinite μ] [SFinite ν]
  证明: by
  ext s hs
  simp_rw [compProd_apply hs, prod_apply hs, Kernel.const_apply]

Depends on / 依赖: Kernel, Kernel.const_apply, compProd_apply, const_apply, prod_apply, simp_rw
-/
lemma compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] :
    μ otimesₘ (Kernel.const α ν) = μ.prod ν := by
  ext s hs
  simp_rw [compProd_apply hs, prod_apply hs, Kernel.const_apply]

/--
lemma `compProd_add_left` / 引理 `compProd_add_left`

English:
lemma compProd_add_left
  given: (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : Kernel α β)
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  · simp_rw [Measure.compProd, Kernel.const_add, Kernel.compProd_add_left, _root_.add_apply]
  · simp [hκ]

中文:
引理 compProd_add_left
  条件: (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : Kernel α β)
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  · simp_rw [Measure.compProd, Kernel.const_add, Kernel.compProd_add_left, _root_.add_apply]
  · simp [hκ]

Depends on / 依赖: IsSFiniteKernel, Kernel, Kernel.compProd_add_left, Kernel.const_add, Measure, Measure.compProd, _root_, _root_.add_apply, add_apply, compProd, compProd_add_left, const_add, simp_rw
-/
lemma compProd_add_left (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : Kernel α β) :
    (μ + ν) otimesₘ κ = μ otimesₘ κ + ν otimesₘ κ := by
  by_cases hκ : IsSFiniteKernel κ
  · simp_rw [Measure.compProd, Kernel.const_add, Kernel.compProd_add_left, _root_.add_apply]
  · simp [hκ]

/--
lemma `compProd_add_right` / 引理 `compProd_add_right`

English:
lemma compProd_add_right
  statement: (μ : Measure α) (κ η : Kernel α β)
  proof: by
  by_cases hμ : SFinite μ
  · simp_rw [Measure.compProd, Kernel.prodMkLeft_add, Kernel.compProd_add_right, _root_.add_apply]
  · simp [hμ]

中文:
引理 compProd_add_right
  结论: (μ : Measure α) (κ η : Kernel α β)
  证明: by
  by_cases hμ : SFinite μ
  · simp_rw [Measure.compProd, Kernel.prodMkLeft_add, Kernel.compProd_add_right, _root_.add_apply]
  · simp [hμ]

Depends on / 依赖: Kernel, Kernel.compProd_add_right, Kernel.prodMkLeft_add, Measure, Measure.compProd, SFinite, _root_, _root_.add_apply, add_apply, compProd, compProd_add_right, prodMkLeft_add, simp_rw
-/
lemma compProd_add_right (μ : Measure α) (κ η : Kernel α β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ otimesₘ (κ + η) = μ otimesₘ κ + μ otimesₘ η := by
  by_cases hμ : SFinite μ
  · simp_rw [Measure.compProd, Kernel.prodMkLeft_add, Kernel.compProd_add_right, _root_.add_apply]
  · simp [hμ]

/--
lemma `compProd_sum_left` / 引理 `compProd_sum_left`

English:
lemma compProd_sum_left
  given: {ι : Type*} [Countable ι] {μ : ι -> Measure α} [forall i, SFinite (μ i)]
  proof: by
  rw [compProd]; rw [← Kernel.sum_const]; rw [Kernel.compProd_sum_left]
  rfl

中文:
引理 compProd_sum_left
  条件: {ι : 类型} [Countable ι] {μ : ι -> Measure α} [对任意 i, SFinite (μ i)]
  证明: by
  rw [compProd]; rw [← Kernel.sum_const]; rw [Kernel.compProd_sum_left]
  rfl

Depends on / 依赖: Kernel, Kernel.compProd_sum_left, Kernel.sum_const, compProd, compProd_sum_left, sum_const
-/
lemma compProd_sum_left {ι : Type*} [Countable ι] {μ : ι -> Measure α} [forall i, SFinite (μ i)] :
    (sum μ) otimesₘ κ = sum (fun i => (μ i) otimesₘ κ) := by
  rw [compProd]; rw [← Kernel.sum_const]; rw [Kernel.compProd_sum_left]
  rfl

/--
lemma `compProd_sum_right` / 引理 `compProd_sum_right`

English:
lemma compProd_sum_right
  statement: {ι : Type*} [Countable ι] {κ : ι -> Kernel α β}
  proof: by
  rw [compProd]; rw [← Kernel.sum_prodMkLeft]; rw [Kernel.compProd_sum_right]
  rfl

@[simp]

中文:
引理 compProd_sum_right
  结论: {ι : 类型} [Countable ι] {κ : ι -> Kernel α β}
  证明: by
  rw [compProd]; rw [← Kernel.sum_prodMkLeft]; rw [Kernel.compProd_sum_right]
  rfl

@[simp]

Depends on / 依赖: Kernel, Kernel.compProd_sum_right, Kernel.sum_prodMkLeft, compProd, compProd_sum_right, sum_prodMkLeft
-/
lemma compProd_sum_right {ι : Type*} [Countable ι] {κ : ι -> Kernel α β}
    [h : forall i, IsSFiniteKernel (κ i)] :
    μ otimesₘ (Kernel.sum κ) = sum (fun i => μ otimesₘ (κ i)) := by
  rw [compProd]; rw [← Kernel.sum_prodMkLeft]; rw [Kernel.compProd_sum_right]
  rfl

@[simp]
/--
lemma `fst_compProd` / 引理 `fst_compProd`

English:
lemma fst_compProd
  given: (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ]
  proof: by
  ext s
  rw [compProd]; rw [Measure.fst]; rw [← Kernel.fst_apply]; rw [Kernel.fst_compProd]; rw [Kernel.const_apply]

中文:
引理 fst_compProd
  条件: (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ]
  证明: by
  ext s
  rw [compProd]; rw [Measure.fst]; rw [← Kernel.fst_apply]; rw [Kernel.fst_compProd]; rw [Kernel.const_apply]

Depends on / 依赖: Kernel, Kernel.const_apply, Kernel.fst_apply, Kernel.fst_compProd, Measure, Measure.fst, compProd, const_apply, fst_apply, fst_compProd
-/
lemma fst_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] :
    (μ otimesₘ κ).fst = μ := by
  ext s
  rw [compProd]; rw [Measure.fst]; rw [← Kernel.fst_apply]; rw [Kernel.fst_compProd]; rw [Kernel.const_apply]

/--
lemma `compProd_smul_left` / 引理 `compProd_smul_left`

English:
lemma compProd_smul_left
  given: (a : Real>=0∞) [SFinite μ] [IsSFiniteKernel κ]
  proof: by
  ext s hs
  simp only [compProd_apply hs, lintegral_smul_measure, smul_apply, smul_eq_mul]

中文:
引理 compProd_smul_left
  条件: (a : 实数>=0∞) [SFinite μ] [IsSFiniteKernel κ]
  证明: by
  ext s hs
  simp only [compProd_apply hs, lintegral_smul_measure, smul_apply, smul_eq_mul]

Depends on / 依赖: compProd_apply, lintegral_smul_measure, smul_apply, smul_eq_mul
-/
lemma compProd_smul_left (a : Real>=0∞) [SFinite μ] [IsSFiniteKernel κ] :
    (a • μ) otimesₘ κ = a • (μ otimesₘ κ) := by
  ext s hs
  simp only [compProd_apply hs, lintegral_smul_measure, smul_apply, smul_eq_mul]

section Integral

/--
lemma `lintegral_compProd` / 引理 `lintegral_compProd`

English:
lemma lintegral_compProd
  statement: [SFinite μ] [IsSFiniteKernel κ]
  proof: by
  rw [compProd]; rw [Kernel.lintegral_compProd _ _ _ hf]
  simp

中文:
引理 lintegral_compProd
  结论: [SFinite μ] [IsSFiniteKernel κ]
  证明: by
  rw [compProd]; rw [Kernel.lintegral_compProd _ _ _ hf]
  simp

Depends on / 依赖: Kernel, Kernel.lintegral_compProd, compProd, lintegral_compProd
-/
lemma lintegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β -> Real>=0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(μ otimesₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd]; rw [Kernel.lintegral_compProd _ _ _ hf]
  simp

/--
lemma `setLIntegral_compProd` / 引理 `setLIntegral_compProd`

English:
lemma setLIntegral_compProd
  statement: [SFinite μ] [IsSFiniteKernel κ]
  proof: by
  rw [compProd]; rw [Kernel.setLIntegral_compProd _ _ _ hf hs ht]
  simp

中文:
引理 setLIntegral_compProd
  结论: [SFinite μ] [IsSFiniteKernel κ]
  证明: by
  rw [compProd]; rw [Kernel.setLIntegral_compProd _ _ _ hf hs ht]
  simp

Depends on / 依赖: Kernel, Kernel.setLIntegral_compProd, compProd, setLIntegral_compProd
-/
lemma setLIntegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β -> Real>=0∞} (hf : Measurable f)
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ x in s ×ˢ t, f x ∂(μ otimesₘ κ) = ∫⁻ a in s, ∫⁻ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd]; rw [Kernel.setLIntegral_compProd _ _ _ hf hs ht]
  simp

end Integral

/--
lemma `dirac_compProd_apply` / 引理 `dirac_compProd_apply`

English:
lemma dirac_compProd_apply
  statement: [MeasurableSingletonClass α] {a : α} [IsSFiniteKernel κ]
  proof: by
  rw [compProd_apply hs]; rw [lintegral_dirac]

中文:
引理 dirac_compProd_apply
  结论: [MeasurableSingletonClass α] {a : α} [IsSFiniteKernel κ]
  证明: by
  rw [compProd_apply hs]; rw [lintegral_dirac]

Depends on / 依赖: compProd_apply, isTopologicallyNilpotent_of_constantCoeff_isNilpotent, lintegral_dirac
-/
lemma dirac_compProd_apply [MeasurableSingletonClass α] {a : α} [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (Measure.dirac a otimesₘ κ) s = κ a (Prod.mk a ⁻¹' s) := by
  rw [compProd_apply hs]; rw [lintegral_dirac]

/--
lemma `dirac_unit_compProd` / 引理 `dirac_unit_compProd`

English:
lemma dirac_unit_compProd
  given: (κ : Kernel Unit β) [IsSFiniteKernel κ]
  proof: by
  ext s hs; rw [dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]

中文:
引理 dirac_unit_compProd
  条件: (κ : Kernel Unit β) [IsSFiniteKernel κ]
  证明: by
  ext s hs; rw [dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]

Depends on / 依赖: Measure, Measure.map_apply, dirac_compProd_apply, map_apply, measurable_prodMk_left
-/
lemma dirac_unit_compProd (κ : Kernel Unit β) [IsSFiniteKernel κ] :
    Measure.dirac () otimesₘ κ = (κ ()).map (Prod.mk ()) := by
  ext s hs; rw [dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]

/--
lemma `dirac_unit_compProd_const` / 引理 `dirac_unit_compProd_const`

English:
lemma dirac_unit_compProd_const
  given: (μ : Measure β) [SFinite μ]
  proof: by
  rw [dirac_unit_compProd]; rw [Kernel.const_apply]

中文:
引理 dirac_unit_compProd_const
  条件: (μ : Measure β) [SFinite μ]
  证明: by
  rw [dirac_unit_compProd]; rw [Kernel.const_apply]

Depends on / 依赖: Kernel, Kernel.const_apply, const_apply, dirac_unit_compProd
-/
lemma dirac_unit_compProd_const (μ : Measure β) [SFinite μ] :
    Measure.dirac () otimesₘ Kernel.const Unit μ = μ.map (Prod.mk ()) := by
  rw [dirac_unit_compProd]; rw [Kernel.const_apply]

/--
lemma `snd_dirac_unit_compProd_const` / 引理 `snd_dirac_unit_compProd_const`

English:
lemma snd_dirac_unit_compProd_const
  given: (μ : Measure β) [SFinite μ]
  proof: by simp

中文:
引理 snd_dirac_unit_compProd_const
  条件: (μ : Measure β) [SFinite μ]
  证明: by simp

Depends on / 依赖: HasSubst, MvPowerSeries, MvPowerSeries.HasSubst.zero, hasSubst_iff
-/
lemma snd_dirac_unit_compProd_const (μ : Measure β) [SFinite μ] :
    snd (Measure.dirac () otimesₘ Kernel.const Unit μ) = μ := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SFinite (μ otimesₘ κ)
  body: by rw [compProd]; infer_instance

中文:
实例 :
  签名: SFinite (μ otimesₘ κ)
  定义体: by rw [compProd]; infer_instance

Depends on / 依赖: compProd, infer_instance
-/
instance : SFinite (μ otimesₘ κ) := by rw [compProd]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteMeasure
  signature: μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ otimesₘ κ)
  body: by
  rw [compProd]; infer_instance

中文:
实例 [IsFiniteMeasure
  签名: μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ otimesₘ κ)
  定义体: by
  rw [compProd]; infer_instance

Depends on / 依赖: Commute, Commute.all, compProd, infer_instance, isNilpotent_add
-/
instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ otimesₘ κ) := by
  rw [compProd]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsProbabilityMeasure
  signature: μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ otimesₘ κ)
  body: by
  rw [compProd]; infer_instance

中文:
实例 [IsProbabilityMeasure
  签名: μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ otimesₘ κ)
  定义体: by
  rw [compProd]; infer_instance

Depends on / 依赖: Commute, Commute.all, HasSubst, compProd, infer_instance, isNilpotent_mul_right, map_mul
-/
instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ otimesₘ κ) := by
  rw [compProd]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsZeroOrProbabilityMeasure
  signature: μ] [IsZeroOrMarkovKernel κ] :
  body: by
  rw [compProd]
  exact IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure ()

中文:
实例 [IsZeroOrProbabilityMeasure
  签名: μ] [IsZeroOrMarkovKernel κ] :
  定义体: by
  rw [compProd]
  exact IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure ()

Depends on / 依赖: Commute, Commute.all, HasSubst, IsZeroOrMarkovKernel, IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure, compProd, isNilpotent_mul_left, isZeroOrProbabilityMeasure, map_mul
-/
instance [IsZeroOrProbabilityMeasure μ] [IsZeroOrMarkovKernel κ] :
    IsZeroOrProbabilityMeasure (μ otimesₘ κ) := by
  rw [compProd]
  exact IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure ()

/-- `Measure.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc`
because the products of types `α × β × γ` and `(α × β) × γ` are different. -/
@[simp]
/--
lemma `compProd_assoc` / 引理 `compProd_assoc`

English:
lemma compProd_assoc
  given: {γ : Type*} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ}
  proof: by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext s hs
  rw [Measure.compProd_apply hs]; rw [Measure.map_apply (by fun_prop) hs]; rw [Measure.compProd_apply (hs.preimage (by fun_prop))]; 

中文:
引理 compProd_assoc
  条件: {γ : 类型} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ}
  证明: by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext s hs
  rw [Measure.compProd_apply hs]; rw [Measure.map_apply (by fun_prop) hs]; rw [Measure.compProd_apply (hs.preimage (by fun_prop))]; 

Depends on / 依赖: IsSFiniteKernel, Kernel, Kernel.compProd_apply, Kernel.measurable_kernel_prodMk_left, Measure, Measure.compProd_apply, Measure.lintegral_compProd, Measure.map_apply, SFinite, compProd_apply, fun_prop, ha.mul_right, hs.preimage, lintegral_compProd, map_apply, measurable_kernel_prodMk_left, mul_right, preimage
-/
lemma compProd_assoc {γ : Type*} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ} :
    (μ otimesₘ (κ otimesₖ η)).map MeasurableEquiv.prodAssoc.symm = μ otimesₘ κ otimesₘ η := by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext s hs
  rw [Measure.compProd_apply hs]; rw [Measure.map_apply (by fun_prop) hs]; rw [Measure.compProd_apply (hs.preimage (by fun_prop))]; rw [Measure.lintegral_compProd]
  swap; · exact Kernel.measurable_kernel_prodMk_left hs
  congr with a
  rw [Kernel.compProd_apply]
  · congr
  · exact hs.preimage (by fun_prop)

/-- `Measure.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc`
because the products of types `α × β × γ` and `(α × β) × γ` are different. -/
@[simp]
/--
lemma `compProd_assoc'` / 引理 `compProd_assoc'`

English:
lemma compProd_assoc'
  given: {γ : Type*} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ}
  proof: by
  simp [← Measure.compProd_assoc]

中文:
引理 compProd_assoc'
  条件: {γ : 类型} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ}
  证明: by
  simp [← Measure.compProd_assoc]

Depends on / 依赖: Measure, Measure.compProd_assoc, compProd_assoc
-/
lemma compProd_assoc' {γ : Type*} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ} :
    (μ otimesₘ κ otimesₘ η).map MeasurableEquiv.prodAssoc = μ otimesₘ (κ otimesₖ η) := by
  simp [← Measure.compProd_assoc]

section AbsolutelyContinuous

/--
lemma `AbsolutelyContinuous.compProd_left` / 引理 `AbsolutelyContinuous.compProd_left`

English:
lemma AbsolutelyContinuous.compProd_left
  given: [SFinite ν] (hμν : μ ≪ ν) (κ : Kernel α β)
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  · have : SFinite μ := sFinite_of_absolutelyContinuous hμν
    refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
    rw [Measure.compProd_apply hs]; rw [lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    exact hμν

中文:
引理 AbsolutelyContinuous.compProd_left
  条件: [SFinite ν] (hμν : μ ≪ ν) (κ : Kernel α β)
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  · have : SFinite μ := sFinite_of_absolutelyContinuous hμν
    refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
    rw [Measure.compProd_apply hs]; rw [lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    exact hμν

Depends on / 依赖: AbsolutelyContinuous, IsSFiniteKernel, Kernel, Kernel.measurable_kernel_prodMk_left, Measure, Measure.AbsolutelyContinuous.mk, Measure.compProd_apply, SFinite, ae_eq, compProd_apply, compProd_of_not_isSFiniteKernel, hs_zero, lintegral_eq_zero_iff, measurable_kernel_prodMk_left, sFinite_of_absolutelyContinuous
-/
lemma AbsolutelyContinuous.compProd_left [SFinite ν] (hμν : μ ≪ ν) (κ : Kernel α β) :
    μ otimesₘ κ ≪ ν otimesₘ κ := by
  by_cases hκ : IsSFiniteKernel κ
  · have : SFinite μ := sFinite_of_absolutelyContinuous hμν
    refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
    rw [Measure.compProd_apply hs]; rw [lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    exact hμν.ae_eq hs_zero
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]

/--
lemma `AbsolutelyContinuous.compProd_right` / 引理 `AbsolutelyContinuous.compProd_right`

English:
lemma AbsolutelyContinuous.compProd_right
  statement: [SFinite μ] [IsSFiniteKernel η]
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  · refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
    rw [Measure.compProd_apply hs]; rw [lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zer

中文:
引理 AbsolutelyContinuous.compProd_right
  结论: [SFinite μ] [IsSFiniteKernel η]
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  · refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
    rw [Measure.compProd_apply hs]; rw [lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zer

Depends on / 依赖: AbsolutelyContinuous, HasSubst, HasSubst.X, IsSFiniteKernel, Kernel, Kernel.measurable_kernel_prodMk_left, Measure, Measure.AbsolutelyContinuous.mk, Measure.compProd_apply, compProd_apply, compProd_of_not_isSFiniteKernel, filter_upwards, ha_ac, ha_zero, hs_zero, lintegral_eq_zero_iff, measurable_kernel_prodMk_left
-/
lemma AbsolutelyContinuous.compProd_right [SFinite μ] [IsSFiniteKernel η]
    (hκη : forallᵐ a ∂μ, κ a ≪ η a) :
    μ otimesₘ κ ≪ μ otimesₘ η := by
  by_cases hκ : IsSFiniteKernel κ
  · refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
    rw [Measure.compProd_apply hs]; rw [lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]

/--
lemma `AbsolutelyContinuous.compProd` / 引理 `AbsolutelyContinuous.compProd`

English:
lemma AbsolutelyContinuous.compProd
  statement: [SFinite ν] [IsSFiniteKernel η]
  proof: have : SFinite μ := sFinite_of_absolutelyContinuous hμν
  (Measure.AbsolutelyContinuous.compProd_right hκη).trans (hμν.compProd_left _)

中文:
引理 AbsolutelyContinuous.compProd
  结论: [SFinite ν] [IsSFiniteKernel η]
  证明: have : SFinite μ := sFinite_of_absolutelyContinuous hμν
  (Measure.AbsolutelyContinuous.compProd_right hκη).trans (hμν.compProd_left _)

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.compProd_right, SFinite, compProd_left, compProd_right, sFinite_of_absolutelyContinuous
-/
lemma AbsolutelyContinuous.compProd [SFinite ν] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : forallᵐ a ∂μ, κ a ≪ η a) :
    μ otimesₘ κ ≪ ν otimesₘ η :=
  have : SFinite μ := sFinite_of_absolutelyContinuous hμν
  (Measure.AbsolutelyContinuous.compProd_right hκη).trans (hμν.compProd_left _)

/--
lemma `absolutelyContinuous_of_compProd` / 引理 `absolutelyContinuous_of_compProd`

English:
lemma absolutelyContinuous_of_compProd
  statement: [SFinite μ] [IsSFiniteKernel κ] [h_zero : forall a, NeZero (κ a)]
  proof: by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 => ?_)
  have h1 : (ν otimesₘ η) (s ×ˢ univ) = 0 := by
    by_cases hν : SFinite ν
    swap; · simp [compProd_of_not_sfinite _ _ hν]
    by_cases hη : IsSFiniteKernel η
    swap; · simp [compProd_of_not_isSFiniteKernel _ _ hη]
    rw [Measure

中文:
引理 absolutelyContinuous_of_compProd
  结论: [SFinite μ] [IsSFiniteKernel κ] [h_zero : 对任意 a, NeZero (κ a)]
  证明: by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 => ?_)
  have h1 : (ν otimesₘ η) (s ×ˢ univ) = 0 := by
    by_cases hν : SFinite ν
    swap; · simp [compProd_of_not_sfinite _ _ hν]
    by_cases hη : IsSFiniteKernel η
    swap; · simp [compProd_of_not_isSFiniteKernel _ _ hη]
    rw [Measure

Depends on / 依赖: AbsolutelyContinuous, IsSFiniteKernel, MeasurableSet, MeasurableSet.univ, Measure, Measure.AbsolutelyContinuous.mk, Measure.compProd_apply_prod, SFinite, compProd_apply_prod, compProd_of_not_isSFiniteKernel, compProd_of_not_sfinite, lintegral_eq_zero_iff, setLIntegral_measure_zero
-/
lemma absolutelyContinuous_of_compProd [SFinite μ] [IsSFiniteKernel κ] [h_zero : forall a, NeZero (κ a)]
    (h : μ otimesₘ κ ≪ ν otimesₘ η) :
    μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 => ?_)
  have h1 : (ν otimesₘ η) (s ×ˢ univ) = 0 := by
    by_cases hν : SFinite ν
    swap; · simp [compProd_of_not_sfinite _ _ hν]
    by_cases hη : IsSFiniteKernel η
    swap; · simp [compProd_of_not_isSFiniteKernel _ _ hη]
    rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
    exact setLIntegral_measure_zero _ _ hs0
  have h2 : (μ otimesₘ κ) (s ×ˢ univ) = 0 := h h1
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ]; rw [lintegral_eq_zero_iff] at h2
  swap; · exact Kernel.measurable_coe _ MeasurableSet.univ
  by_contra hμs
  have : Filter.NeBot (ae (μ.restrict s)) := by simp [hμs]
  obtain ⟨a, ha⟩ : exists a, κ a univ = 0 := h2.exists
  refine absurd ha ?_
  simp only [Measure.measure_univ_eq_zero]
  exact (h_zero a).out

/--
lemma `absolutelyContinuous_compProd_left_iff` / 引理 `absolutelyContinuous_compProd_left_iff`

English:
lemma absolutelyContinuous_compProd_left_iff
  statement: [SFinite μ] [SFinite ν]
  proof: ⟨absolutelyContinuous_of_compProd, fun h => h.compProd_left κ⟩

中文:
引理 absolutelyContinuous_compProd_left_iff
  结论: [SFinite μ] [SFinite ν]
  证明: ⟨absolutelyContinuous_of_compProd, fun h => h.compProd_left κ⟩

Depends on / 依赖: absolutelyContinuous_of_compProd, compProd_left, h.compProd_left
-/
lemma absolutelyContinuous_compProd_left_iff [SFinite μ] [SFinite ν]
    [IsSFiniteKernel κ] [forall a, NeZero (κ a)] :
    μ otimesₘ κ ≪ ν otimesₘ κ ↔ μ ≪ ν :=
  ⟨absolutelyContinuous_of_compProd, fun h => h.compProd_left κ⟩

/--
lemma `AbsolutelyContinuous.compProd_of_compProd` / 引理 `AbsolutelyContinuous.compProd_of_compProd`

English:
lemma AbsolutelyContinuous.compProd_of_compProd
  statement: [SFinite ν] [IsSFiniteKernel η]
  proof: by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  refine AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  suffices (μ otimesₘ η) s = 0 from hκη this
  rw [measure_eq_zero_iff_ae_notMem]; rw [ae_compProd_iff hs.compl] at hs_zero ⊢
  exact hμν.ae_le hs_zero

中文:
引理 AbsolutelyContinuous.compProd_of_compProd
  结论: [SFinite ν] [IsSFiniteKernel η]
  证明: by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  refine AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  suffices (μ otimesₘ η) s = 0 from hκη this
  rw [measure_eq_zero_iff_ae_notMem]; rw [ae_compProd_iff hs.compl] at hs_zero ⊢
  exact hμν.ae_le hs_zero

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, SFinite, ae_compProd_iff, ae_le, compProd_of_not_sfinite, hs.compl, hs_zero, measure_eq_zero_iff_ae_notMem
-/
lemma AbsolutelyContinuous.compProd_of_compProd [SFinite ν] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : μ otimesₘ κ ≪ μ otimesₘ η) :
    μ otimesₘ κ ≪ ν otimesₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  refine AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  suffices (μ otimesₘ η) s = 0 from hκη this
  rw [measure_eq_zero_iff_ae_notMem]; rw [ae_compProd_iff hs.compl] at hs_zero ⊢
  exact hμν.ae_le hs_zero

end AbsolutelyContinuous

section MutuallySingular

/--
lemma `MutuallySingular.compProd_of_left` / 引理 `MutuallySingular.compProd_of_left`

English:
lemma MutuallySingular.compProd_of_left
  given: (hμν : μ ⟂ₘ ν) (κ η : Kernel α β)
  proof: by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  by_cases hκ : IsSFiniteKernel κ
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hκ]; simp
  by_cases hη : IsSFiniteKernel η
  swap; · rw 

中文:
引理 MutuallySingular.compProd_of_left
  条件: (hμν : μ ⟂ₘ ν) (κ η : Kernel α β)
  证明: by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  by_cases hκ : IsSFiniteKernel κ
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hκ]; simp
  by_cases hη : IsSFiniteKernel η
  swap; · rw 

Depends on / 依赖: IsSFiniteKernel, SFinite, compProd_apply_prod, compProd_of_not_isSFiniteKernel, compProd_of_not_sfinite, compl_prod_eq_union, measurableSet_nullSet, measurableSet_nullSet.prod, nullSet
-/
lemma MutuallySingular.compProd_of_left (hμν : μ ⟂ₘ ν) (κ η : Kernel α β) :
    μ otimesₘ κ ⟂ₘ ν otimesₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  by_cases hκ : IsSFiniteKernel κ
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hκ]; simp
  by_cases hη : IsSFiniteKernel η
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hη]; simp
  refine ⟨hμν.nullSet ×ˢ univ, hμν.measurableSet_nullSet.prod .univ, ?_⟩
  rw [compProd_apply_prod hμν.measurableSet_nullSet .univ]; rw [compl_prod_eq_union]
  simp only [MutuallySingular.restrict_nullSet, lintegral_zero_measure, compl_univ,
    prod_empty, union_empty, true_and]
  rw [compProd_apply_prod hμν.measurableSet_nullSet.compl .univ]
  simp

/--
lemma `mutuallySingular_of_mutuallySingular_compProd` / 引理 `mutuallySingular_of_mutuallySingular_compProd`

English:
lemma mutuallySingular_of_mutuallySingular_compProd
  statement: {ξ : Measure α}
  proof: by
  have hs : MeasurableSet h.nullSet := h.measurableSet_nullSet
  have hμ_zero : (μ otimesₘ κ) h.nullSet = 0 := h.measure_nullSet
  have hν_zero : (ν otimesₘ η) h.nullSetᶜ = 0 := h.measure_compl_nullSet
  rw [compProd_apply]; rw [lintegral_eq_zero_iff'] at hμ_zero hν_zero
  · filter_upwards [hμ hμ

中文:
引理 mutuallySingular_of_mutuallySingular_compProd
  结论: {ξ : Measure α}
  证明: by
  have hs : MeasurableSet h.nullSet := h.measurableSet_nullSet
  have hμ_zero : (μ otimesₘ κ) h.nullSet = 0 := h.measure_nullSet
  have hν_zero : (ν otimesₘ η) h.nullSetᶜ = 0 := h.measure_compl_nullSet
  rw [compProd_apply]; rw [lintegral_eq_zero_iff'] at hμ_zero hν_zero
  · filter_upwards [hμ hμ

Depends on / 依赖: Kernel, Kernel.measurable_kernel_pr, Kernel.measurable_kernel_prodMk_left, MeasurableSet, Prod.mk, aemeasurable, compProd_apply, filter_upwards, h.measurableSet_nullSet, h.measure_compl_nullSet, h.measure_nullSet, h.nullSet, hs.compl, lintegral_eq_zero_iff, measurableSet_nullSet, measurable_kernel_pr, measurable_kernel_prodMk_left, measurable_prodMk_left, measure_compl_nullSet, measure_nullSet
-/
lemma mutuallySingular_of_mutuallySingular_compProd {ξ : Measure α}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : μ otimesₘ κ ⟂ₘ ν otimesₘ η) (hμ : ξ ≪ μ) (hν : ξ ≪ ν) :
    forallᵐ x ∂ξ, κ x ⟂ₘ η x := by
  have hs : MeasurableSet h.nullSet := h.measurableSet_nullSet
  have hμ_zero : (μ otimesₘ κ) h.nullSet = 0 := h.measure_nullSet
  have hν_zero : (ν otimesₘ η) h.nullSetᶜ = 0 := h.measure_compl_nullSet
  rw [compProd_apply]; rw [lintegral_eq_zero_iff'] at hμ_zero hν_zero
  · filter_upwards [hμ hμ_zero, hν hν_zero] with x hxμ hxν
    exact ⟨Prod.mk x ⁻¹' h.nullSet, measurable_prodMk_left hs, ⟨hxμ, hxν⟩⟩
  · exact (Kernel.measurable_kernel_prodMk_left hs.compl).aemeasurable
  · exact (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
  · exact hs.compl
  · exact hs

/--
lemma `mutuallySingular_compProd_left_iff` / 引理 `mutuallySingular_compProd_left_iff`

English:
lemma mutuallySingular_compProd_left_iff
  statement: [SFinite μ] [SigmaFinite ν]
  proof: by
  refine ⟨fun h => ?_, fun h => h.compProd_of_left _ _⟩
  rw [← withDensity_rnDeriv_eq_zero]
  have hh := mutuallySingular_of_mutuallySingular_compProd h ?_ ?_
    (ξ := ν.withDensity (μ.rnDeriv ν))
  rotate_left
  · exact absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)
  · exact withDens

中文:
引理 mutuallySingular_compProd_left_iff
  结论: [SFinite μ] [SigmaFinite ν]
  证明: by
  refine ⟨fun h => ?_, fun h => h.compProd_of_left _ _⟩
  rw [← withDensity_rnDeriv_eq_zero]
  have hh := mutuallySingular_of_mutuallySingular_compProd h ?_ ?_
    (ξ := ν.withDensity (μ.rnDeriv ν))
  rotate_left
  · exact absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)
  · exact withDens

Depends on / 依赖: Filter, Filter.eventually_false_iff_eq_bot.mp, MutuallySingular, MutuallySingular.self_iff, absolutelyContinuous_of_le, ae_eq_bot, ae_eq_bot.mp, compProd_of_left, eventually_false_iff_eq_bot, h.compProd_of_left, mutuallySingular_of_mutuallySingular_compProd, rnDeriv, rotate_left, self_iff, simp_rw, withDensity, withDensity_absolutelyContinuous, withDensity_rnDeriv_eq_zero, withDensity_rnDeriv_le
-/
lemma mutuallySingular_compProd_left_iff [SFinite μ] [SigmaFinite ν]
    [IsSFiniteKernel κ] [hκ : forall x, NeZero (κ x)] :
    μ otimesₘ κ ⟂ₘ ν otimesₘ κ ↔ μ ⟂ₘ ν := by
  refine ⟨fun h => ?_, fun h => h.compProd_of_left _ _⟩
  rw [← withDensity_rnDeriv_eq_zero]
  have hh := mutuallySingular_of_mutuallySingular_compProd h ?_ ?_
    (ξ := ν.withDensity (μ.rnDeriv ν))
  rotate_left
  · exact absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)
  · exact withDensity_absolutelyContinuous _ _
  simp_rw [MutuallySingular.self_iff, (hκ _).ne] at hh
  exact ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hh)

/--
lemma `AbsolutelyContinuous.mutuallySingular_compProd_iff` / 引理 `AbsolutelyContinuous.mutuallySingular_compProd_iff`

English:
lemma AbsolutelyContinuous.mutuallySingular_compProd_iff
  statement: [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  conv_lhs => rw [ν.haveLebesgueDecomposition_add μ]
  rw [compProd_add_left]; rw [MutuallySingular.add_right_iff]
  simp only [(mutuallySingular_singularPart ν μ).symm.compProd_of_left κ η, true_and]
  refine ⟨fun h => h.mono_ac .rfl ?_, fun h => h.mono_ac .rfl ?_⟩
  · exact (absolutelyContinuou

中文:
引理 AbsolutelyContinuous.mutuallySingular_compProd_iff
  结论: [SigmaFinite μ] [SigmaFinite ν]
  证明: by
  conv_lhs => rw [ν.haveLebesgueDecomposition_add μ]
  rw [compProd_add_left]; rw [MutuallySingular.add_right_iff]
  simp only [(mutuallySingular_singularPart ν μ).symm.compProd_of_left κ η, true_and]
  refine ⟨fun h => h.mono_ac .rfl ?_, fun h => h.mono_ac .rfl ?_⟩
  · exact (absolutelyContinuou

Depends on / 依赖: MutuallySingular, MutuallySingular.add_right_iff, absolutelyContinuous_withDensity_rnDeriv, add_right_iff, compProd_add_left, compProd_left, compProd_of_left, conv_lhs, h.mono_ac, haveLebesgueDecomposition_add, mono_ac, mutuallySingular_singularPart, rnDeriv, symm.compProd_of_left, true_and, withDensity_absolutelyContinuous
-/
lemma AbsolutelyContinuous.mutuallySingular_compProd_iff [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) :
    μ otimesₘ κ ⟂ₘ ν otimesₘ η ↔ μ otimesₘ κ ⟂ₘ μ otimesₘ η := by
  conv_lhs => rw [ν.haveLebesgueDecomposition_add μ]
  rw [compProd_add_left]; rw [MutuallySingular.add_right_iff]
  simp only [(mutuallySingular_singularPart ν μ).symm.compProd_of_left κ η, true_and]
  refine ⟨fun h => h.mono_ac .rfl ?_, fun h => h.mono_ac .rfl ?_⟩
  · exact (absolutelyContinuous_withDensity_rnDeriv hμν).compProd_left _
  · exact (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).compProd_left _

/--
lemma `mutuallySingular_compProd_iff` / 引理 `mutuallySingular_compProd_iff`

English:
lemma mutuallySingular_compProd_iff
  given: [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [compProd_add_left]; rw [MutuallySingular.add_left_iff]
  simp only [(mutuallySingular_singularPart μ ν).compProd_of_left κ η, true_and]
  rw [(withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).mutuallySingular_compProd_iff]
  refine ⟨fun 

中文:
引理 mutuallySingular_compProd_iff
  条件: [SigmaFinite μ] [SigmaFinite ν]
  证明: by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [compProd_add_left]; rw [MutuallySingular.add_left_iff]
  simp only [(mutuallySingular_singularPart μ ν).compProd_of_left κ η, true_and]
  rw [(withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).mutuallySingular_compProd_iff]
  refine ⟨fun 

Depends on / 依赖: MutuallySingular, MutuallySingular.add_left_iff, absolutelyCont, add_left_iff, compProd_add_left, compProd_left, compProd_of_left, conv_lhs, h.mono_ac, haveLebesgueDecomposition_add, infer_instance, mono_ac, mutuallySingular_compProd_iff, mutuallySingular_singularPart, rnDeriv, true_and, withDensity_absolutelyContinuous, withDensity_rnDeriv
-/
lemma mutuallySingular_compProd_iff [SigmaFinite μ] [SigmaFinite ν] :
    μ otimesₘ κ ⟂ₘ ν otimesₘ η ↔ forall ξ, SFinite ξ -> ξ ≪ μ -> ξ ≪ ν -> ξ otimesₘ κ ⟂ₘ ξ otimesₘ η := by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [compProd_add_left]; rw [MutuallySingular.add_left_iff]
  simp only [(mutuallySingular_singularPart μ ν).compProd_of_left κ η, true_and]
  rw [(withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).mutuallySingular_compProd_iff]
  refine ⟨fun h ξ hξ hξμ hξν => ?_, fun h => ?_⟩
  · exact h.mono_ac ((hξμ.withDensity_rnDeriv hξν).compProd_left _)
      ((hξμ.withDensity_rnDeriv hξν).compProd_left _)
  · refine h _ ?_ ?_ ?_
    · infer_instance
    · exact absolutelyContinuous_of_le (withDensity_rnDeriv_le _ _)
    · exact withDensity_absolutelyContinuous ν (μ.rnDeriv ν)

end MutuallySingular

/--
lemma `absolutelyContinuous_compProd_of_compProd` / 引理 `absolutelyContinuous_compProd_of_compProd`

English:
lemma absolutelyContinuous_compProd_of_compProd
  statement: [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  rw [ν.haveLebesgueDecomposition_add μ]; rw [compProd_add_left]; rw [add_comm] at hκη
  have h := absolutelyContinuous_of_add_of_mutuallySingular hκη
    ((mutuallySingular_singularPart _ _).symm.compProd_of_left _ _)
  refine h.trans (AbsolutelyContinuous.compProd_left ?_ _)
  exact withDensity

中文:
引理 absolutelyContinuous_compProd_of_compProd
  结论: [SigmaFinite μ] [SigmaFinite ν]
  证明: by
  rw [ν.haveLebesgueDecomposition_add μ]; rw [compProd_add_left]; rw [add_comm] at hκη
  have h := absolutelyContinuous_of_add_of_mutuallySingular hκη
    ((mutuallySingular_singularPart _ _).symm.compProd_of_left _ _)
  refine h.trans (AbsolutelyContinuous.compProd_left ?_ _)
  exact withDensity

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.compProd_left, absolutelyContinuous_of_add_of_mutuallySingular, add_comm, compProd_add_left, compProd_left, compProd_of_left, h.trans, haveLebesgueDecomposition_add, mutuallySingular_singularPart, symm.compProd_of_left, withDensity_absolutelyContinuous
-/
lemma absolutelyContinuous_compProd_of_compProd [SigmaFinite μ] [SigmaFinite ν]
    (hκη : μ otimesₘ κ ≪ ν otimesₘ η) :
    μ otimesₘ κ ≪ μ otimesₘ η := by
  rw [ν.haveLebesgueDecomposition_add μ]; rw [compProd_add_left]; rw [add_comm] at hκη
  have h := absolutelyContinuous_of_add_of_mutuallySingular hκη
    ((mutuallySingular_singularPart _ _).symm.compProd_of_left _ _)
  refine h.trans (AbsolutelyContinuous.compProd_left ?_ _)
  exact withDensity_absolutelyContinuous _ _

/--
lemma `absolutelyContinuous_compProd_iff` / 引理 `absolutelyContinuous_compProd_iff`

English:
lemma absolutelyContinuous_compProd_iff
  proof: ⟨fun h => ⟨absolutelyContinuous_of_compProd h, absolutelyContinuous_compProd_of_compProd h⟩,
    fun h => h.1.compProd_of_compProd h.2⟩

中文:
引理 absolutelyContinuous_compProd_iff
  证明: ⟨fun h => ⟨absolutelyContinuous_of_compProd h, absolutelyContinuous_compProd_of_compProd h⟩,
    fun h => h.1.compProd_of_compProd h.2⟩

Depends on / 依赖: absolutelyContinuous_compProd_of_compProd, absolutelyContinuous_of_compProd, compProd_of_compProd
-/
lemma absolutelyContinuous_compProd_iff
    [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η] [forall x, NeZero (κ x)] :
    μ otimesₘ κ ≪ ν otimesₘ η ↔ μ ≪ ν ∧ μ otimesₘ κ ≪ μ otimesₘ η :=
  ⟨fun h => ⟨absolutelyContinuous_of_compProd h, absolutelyContinuous_compProd_of_compProd h⟩,
    fun h => h.1.compProd_of_compProd h.2⟩

end MeasureTheory.Measure
