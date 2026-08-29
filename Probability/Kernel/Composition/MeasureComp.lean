/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Lemmas about the composition of a measure and a kernel

Basic lemmas about the composition `κ ∘ₘ μ` of a kernel `κ` and a measure `μ`.

-/

public section

open scoped ENNReal

open ProbabilityTheory MeasureTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  given: {η : Kernel β γ}
  statement: η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
  proof: Measure.bind_bind κ.aemeasurable η.aemeasurable

中文:
引理 comp_assoc
  条件: {η : 核 β γ}
  结论: η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
  证明: Measure.bind_bind κ.aemeasurable η.aemeasurable

Depends on / 依赖: Measure, Measure.bind_bind, aemeasurable, bind_bind
-/
lemma comp_assoc {η : Kernel β γ} : η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ :=
  Measure.bind_bind κ.aemeasurable η.aemeasurable

/--
lemma `comp_eq_comp_const_apply` / 引理 `comp_eq_comp_const_apply`

English:
lemma comp_eq_comp_const_apply
  statement: κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) ()
  proof: by
  rw [Kernel.comp_apply]; rw [Kernel.const_apply]

中文:
引理 comp_eq_comp_const_apply
  结论: κ ∘ₘ μ = (κ ∘ₖ (核.const 单元 μ)) ()
  证明: by
  rw [Kernel.comp_apply]; rw [Kernel.const_apply]

Depends on / 依赖: Kernel, Kernel.comp_apply, Kernel.const_apply, comp_apply, const_apply
-/
lemma comp_eq_comp_const_apply : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) () := by
  rw [Kernel.comp_apply]; rw [Kernel.const_apply]

/--
lemma `comp_eq_sum_of_countable` / 引理 `comp_eq_sum_of_countable`

English:
lemma comp_eq_sum_of_countable
  given: [Countable α] [MeasurableSingletonClass α]
  proof: by
  ext s hs
  rw [Measure.sum_apply _ hs]; rw [Measure.bind_apply hs (by fun_prop)]
  simp [lintegral_countable', mul_comm]

@[simp]

中文:
引理 comp_eq_sum_of_countable
  条件: [可数 α] [MeasurableSingleton类 α]
  证明: by
  ext s hs
  rw [Measure.sum_apply _ hs]; rw [Measure.bind_apply hs (by fun_prop)]
  simp [lintegral_countable', mul_comm]

@[simp]

Depends on / 依赖: Measure, Measure.bind_apply, Measure.sum_apply, bind_apply, fun_prop, lintegral_countable, mul_comm, sum_apply
-/
lemma comp_eq_sum_of_countable [Countable α] [MeasurableSingletonClass α] :
    κ ∘ₘ μ = Measure.sum (fun ω => μ {ω} • κ ω) := by
  ext s hs
  rw [Measure.sum_apply _ hs]; rw [Measure.bind_apply hs (by fun_prop)]
  simp [lintegral_countable', mul_comm]

@[simp]
/--
lemma `snd_compProd` / 引理 `snd_compProd`

English:
lemma snd_compProd
  given: (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  ext s hs
  rw [bind_apply hs κ.aemeasurable]; rw [snd_apply hs]; rw [compProd_apply]
  · rfl
  · exact measurable_snd hs

中文:
引理 snd_compProd
  条件: (μ : 测度 α) [SFinite μ] (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  ext s hs
  rw [bind_apply hs κ.aemeasurable]; rw [snd_apply hs]; rw [compProd_apply]
  · rfl
  · exact measurable_snd hs

Depends on / 依赖: aemeasurable, bind_apply, compProd_apply, measurable_snd, snd_apply
-/
lemma snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ otimesₘ κ).snd = κ ∘ₘ μ := by
  ext s hs
  rw [bind_apply hs κ.aemeasurable]; rw [snd_apply hs]; rw [compProd_apply]
  · rfl
  · exact measurable_snd hs

/--
lemma `comp_congr` / 引理 `comp_congr`

English:
lemma comp_congr
  given: (h : forallᵐ a ∂μ, κ a = η a)
  statement: κ ∘ₘ μ = η ∘ₘ μ
  proof: bind_congr_right h

中文:
引理 comp_congr
  条件: (h : 对任意ᵐ a ∂μ, κ a = η a)
  结论: κ ∘ₘ μ = η ∘ₘ μ
  证明: bind_congr_right h

Depends on / 依赖: bind_congr_right
-/
lemma comp_congr (h : forallᵐ a ∂μ, κ a = η a) : κ ∘ₘ μ = η ∘ₘ μ := bind_congr_right h

/--
lemma `ae_ae_of_ae_comp` / 引理 `ae_ae_of_ae_comp`

English:
lemma ae_ae_of_ae_comp
  given: {p : β -> Prop} (h : forallᵐ ω ∂(κ ∘ₘ μ), p ω)
  proof: by
  rw [comp_eq_comp_const_apply] at h
  exact Kernel.ae_ae_of_ae_comp h

中文:
引理 ae_ae_of_ae_comp
  条件: {p : β -> 命题} (h : 对任意ᵐ ω ∂(κ ∘ₘ μ), p ω)
  证明: by
  rw [comp_eq_comp_const_apply] at h
  exact Kernel.ae_ae_of_ae_comp h

Depends on / 依赖: Kernel, Kernel.ae_ae_of_ae_comp, ae_ae_of_ae_comp, comp_eq_comp_const_apply
-/
lemma ae_ae_of_ae_comp {p : β -> Prop} (h : forallᵐ ω ∂(κ ∘ₘ μ), p ω) :
    forallᵐ ω' ∂μ, forallᵐ ω ∂(κ ω'), p ω := by
  rw [comp_eq_comp_const_apply] at h
  exact Kernel.ae_ae_of_ae_comp h

/--
lemma `ae_comp_of_ae_ae` / 引理 `ae_comp_of_ae_ae`

English:
lemma ae_comp_of_ae_ae
  statement: {p : β -> Prop} (hp : MeasurableSet {z | p z})
  proof: by
  rw [comp_eq_comp_const_apply]
  exact Kernel.ae_comp_of_ae_ae hp h

中文:
引理 ae_comp_of_ae_ae
  结论: {p : β -> 命题} (hp : 可测集 {z | p z})
  证明: by
  rw [comp_eq_comp_const_apply]
  exact Kernel.ae_comp_of_ae_ae hp h

Depends on / 依赖: Kernel, Kernel.ae_comp_of_ae_ae, ae_comp_of_ae_ae, comp_eq_comp_const_apply
-/
lemma ae_comp_of_ae_ae {p : β -> Prop} (hp : MeasurableSet {z | p z})
    (h : forallᵐ y ∂μ, forallᵐ z ∂κ y, p z) : forallᵐ z ∂(κ ∘ₘ μ), p z := by
  rw [comp_eq_comp_const_apply]
  exact Kernel.ae_comp_of_ae_ae hp h

/--
lemma `ae_comp_iff` / 引理 `ae_comp_iff`

English:
lemma ae_comp_iff
  given: {p : β -> Prop} (hp : MeasurableSet {z | p z})
  proof: ⟨ae_ae_of_ae_comp, ae_comp_of_ae_ae hp⟩

中文:
引理 ae_comp_iff
  条件: {p : β -> 命题} (hp : 可测集 {z | p z})
  证明: ⟨ae_ae_of_ae_comp, ae_comp_of_ae_ae hp⟩

Depends on / 依赖: ae_ae_of_ae_comp, ae_comp_of_ae_ae
-/
lemma ae_comp_iff {p : β -> Prop} (hp : MeasurableSet {z | p z}) :
    (forallᵐ z ∂(κ ∘ₘ μ), p z) ↔ forallᵐ y ∂μ, forallᵐ z ∂κ y, p z :=
  ⟨ae_ae_of_ae_comp, ae_comp_of_ae_ae hp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SFinite
  signature: μ] [IsSFiniteKernel κ] : SFinite (κ ∘ₘ μ)
  body: by
  rw [← snd_compProd]; infer_instance

中文:
实例 [SFinite
  签名: μ] [是SFiniteKernel κ] : SFinite (κ ∘ₘ μ)
  定义体: by
  rw [← snd_compProd]; infer_instance

Depends on / 依赖: infer_instance, snd_compProd
-/
instance [SFinite μ] [IsSFiniteKernel κ] : SFinite (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteMeasure
  signature: μ] [IsFiniteKernel κ] : IsFiniteMeasure (κ ∘ₘ μ)
  body: by
  rw [← snd_compProd]; infer_instance

中文:
实例 [是有限测度
  签名: μ] [是FiniteKernel κ] : 是有限测度 (κ ∘ₘ μ)
  定义体: by
  rw [← snd_compProd]; infer_instance

Depends on / 依赖: infer_instance, snd_compProd
-/
instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsProbabilityMeasure
  signature: μ] [IsMarkovKernel κ] : IsProbabilityMeasure (κ ∘ₘ μ)
  body: by
  rw [← snd_compProd]; infer_instance

中文:
实例 [是概率测度
  签名: μ] [是MarkovKernel κ] : 是概率测度 (κ ∘ₘ μ)
  定义体: by
  rw [← snd_compProd]; infer_instance

Depends on / 依赖: infer_instance, snd_compProd
-/
instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsZeroOrProbabilityMeasure
  signature: μ] [IsZeroOrMarkovKernel κ] :
  body: by
  rw [← snd_compProd]; infer_instance

@[simp]

中文:
实例 [是ZeroOrProbabilityMeasure
  签名: μ] [是ZeroOrMarkovKernel κ] :
  定义体: by
  rw [← snd_compProd]; infer_instance

@[simp]

Depends on / 依赖: infer_instance, snd_compProd
-/
instance [IsZeroOrProbabilityMeasure μ] [IsZeroOrMarkovKernel κ] :
    IsZeroOrProbabilityMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

@[simp]
/--
lemma `_root_.ProbabilityTheory.Kernel.comp_const` / 引理 `_root_.ProbabilityTheory.Kernel.comp_const`

English:
lemma _root_.ProbabilityTheory.Kernel.comp_const
  given: (κ : Kernel β γ) (μ : Measure β)
  proof: rfl

中文:
引理 _root_.ProbabilityTheory.核.comp_const
  条件: (κ : 核 β γ) (μ : 测度 β)
  证明: rfl
-/
lemma _root_.ProbabilityTheory.Kernel.comp_const (κ : Kernel β γ) (μ : Measure β) :
    κ ∘ₖ Kernel.const α μ = Kernel.const α (κ ∘ₘ μ) := rfl

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (μ : Measure α) (κ : Kernel α β) {f : β -> γ} (hf : Measurable f)
  proof: by
  ext s hs
  rw [Measure.map_apply hf hs]; rw [Measure.bind_apply (hf hs) κ.aemeasurable]; rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Kernel.map_apply' _ hf _ hs]

@[simp]

中文:
引理 map_comp
  条件: (μ : 测度 α) (κ : 核 α β) {f : β -> γ} (hf : 可测 f)
  证明: by
  ext s hs
  rw [Measure.map_apply hf hs]; rw [Measure.bind_apply (hf hs) κ.aemeasurable]; rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Kernel.map_apply' _ hf _ hs]

@[simp]

Depends on / 依赖: Kernel, Kernel.aemeasurable, Kernel.map_apply, Measure, Measure.bind_apply, Measure.map_apply, aemeasurable, bind_apply, map_apply, simp_rw
-/
lemma map_comp (μ : Measure α) (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) :
    (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ := by
  ext s hs
  rw [Measure.map_apply hf hs]; rw [Measure.bind_apply (hf hs) κ.aemeasurable]; rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Kernel.map_apply' _ hf _ hs]

@[simp]
/--
lemma `discard_comp` / 引理 `discard_comp`

English:
lemma discard_comp
  given: (μ : Measure α)
  statement: Kernel.discard α ∘ₘ μ = μ .univ • Measure.dirac ()
  proof: by
  ext s hs; simp [Measure.bind_apply hs (Kernel.aemeasurable _), mul_comm]

中文:
引理 discard_comp
  条件: (μ : 测度 α)
  结论: 核.discard α ∘ₘ μ = μ .univ • 测度.dirac ()
  证明: by
  ext s hs; simp [Measure.bind_apply hs (Kernel.aemeasurable _), mul_comm]

Depends on / 依赖: Kernel, Kernel.aemeasurable, Measure, Measure.bind_apply, aemeasurable, bind_apply, mul_comm
-/
lemma discard_comp (μ : Measure α) : Kernel.discard α ∘ₘ μ = μ .univ • Measure.dirac () := by
  ext s hs; simp [Measure.bind_apply hs (Kernel.aemeasurable _), mul_comm]

/--
lemma `copy_comp_map` / 引理 `copy_comp_map`

English:
lemma copy_comp_map
  given: {f : α -> β} (hf : AEMeasurable f μ)
  proof: by
  rw [Kernel.copy]; rw [deterministic_comp_eq_map]
  exact (aemeasurable_id.prodMk aemeasurable_id).map_map_of_aemeasurable hf

中文:
引理 copy_comp_map
  条件: {f : α -> β} (hf : 几乎处处可测 f μ)
  证明: by
  rw [Kernel.copy]; rw [deterministic_comp_eq_map]
  exact (aemeasurable_id.prodMk aemeasurable_id).map_map_of_aemeasurable hf

Depends on / 依赖: Kernel, Kernel.copy, aemeasurable_id, aemeasurable_id.prodMk, deterministic_comp_eq_map, map_map_of_aemeasurable, prodMk
-/
lemma copy_comp_map {f : α -> β} (hf : AEMeasurable f μ) :
    Kernel.copy β ∘ₘ (μ.map f) = μ.map (Function.prod f f) := by
  rw [Kernel.copy]; rw [deterministic_comp_eq_map]
  exact (aemeasurable_id.prodMk aemeasurable_id).map_map_of_aemeasurable hf

section CompProd

/--
lemma `compProd_eq_comp_prod` / 引理 `compProd_eq_comp_prod`

English:
lemma compProd_eq_comp_prod
  given: (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  rw [compProd]; rw [Kernel.compProd_prodMkLeft_eq_comp]
  rfl

中文:
引理 compProd_eq_comp_prod
  条件: (μ : 测度 α) [SFinite μ] (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  rw [compProd]; rw [Kernel.compProd_prodMkLeft_eq_comp]
  rfl

Depends on / 依赖: Kernel, Kernel.compProd_prodMkLeft_eq_comp, compProd, compProd_prodMkLeft_eq_comp
-/
lemma compProd_eq_comp_prod (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    μ otimesₘ κ = (Kernel.id ×ₖ κ) ∘ₘ μ := by
  rw [compProd]; rw [Kernel.compProd_prodMkLeft_eq_comp]
  rfl

/--
lemma `compProd_id_eq_copy_comp` / 引理 `compProd_id_eq_copy_comp`

English:
lemma compProd_id_eq_copy_comp
  given: [SFinite μ]
  statement: μ otimesₘ Kernel.id = Kernel.copy α ∘ₘ μ
  proof: by
  rw [compProd_id]; rw [Kernel.copy]; rw [deterministic_comp_eq_map]

中文:
引理 compProd_id_eq_copy_comp
  条件: [SFinite μ]
  结论: μ otimesₘ 核.id = 核.copy α ∘ₘ μ
  证明: by
  rw [compProd_id]; rw [Kernel.copy]; rw [deterministic_comp_eq_map]

Depends on / 依赖: Kernel, Kernel.copy, compProd_id, deterministic_comp_eq_map
-/
lemma compProd_id_eq_copy_comp [SFinite μ] : μ otimesₘ Kernel.id = Kernel.copy α ∘ₘ μ := by
  rw [compProd_id]; rw [Kernel.copy]; rw [deterministic_comp_eq_map]

/--
lemma `comp_compProd_comm` / 引理 `comp_compProd_comm`

English:
lemma comp_compProd_comm
  given: {η : Kernel (α × β) γ} [SFinite μ] [IsSFiniteKernel η]
  proof: by
  by_cases hκ : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ,
      Kernel.compProd_of_not_isSFiniteKernel_left _ _ hκ, FunLike.coe_zero]
  ext s hs
  rw [Measure.bind_apply hs η.aemeasurable]; rw [Measure.snd_apply hs]; rw [Measure.bind_apply _ (Kernel.aemeasurable _)]; rw [Measure.lintegral_compProd (η.measurable_coe hs)]
  swap; · exact measurable_snd hs
  congr with a
  rw [Kernel.compProd_apply]
  · rfl
  · exact measurable_snd hs

@[simp]

中文:
引理 comp_compProd_comm
  条件: {η : 核 (α × β) γ} [SFinite μ] [是SFiniteKernel η]
  证明: by
  by_cases hκ : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ,
      Kernel.compProd_of_not_isSFiniteKernel_left _ _ hκ, FunLike.coe_zero]
  ext s hs
  rw [Measure.bind_apply hs η.aemeasurable]; rw [Measure.snd_apply hs]; rw [Measure.bind_apply _ (Kernel.aemeasurable _)]; rw [Measure.lintegral_compProd (η.measurable_coe hs)]
  swap; · exact measurable_snd hs
  congr with a
  rw [Kernel.compProd_apply]
  · rfl
  · exact measurable_snd hs

@[simp]

Depends on / 依赖: FunLike, FunLike.coe_zero, IsSFiniteKernel, Kernel, Kernel.aemeasurable, Kernel.compProd_apply, Kernel.compProd_of_not_isSFiniteKernel_left, Measure, Measure.bind_apply, Measure.lintegral_compProd, Measure.snd_apply, aemeasurable, bind_apply, coe_zero, compProd_apply, compProd_of_not_isSFiniteKernel, compProd_of_not_isSFiniteKernel_left, lintegral_compProd, measurable_coe, measurable_snd
-/
lemma comp_compProd_comm {η : Kernel (α × β) γ} [SFinite μ] [IsSFiniteKernel η] :
    η ∘ₘ (μ otimesₘ κ) = ((κ otimesₖ η) ∘ₘ μ).snd := by
  by_cases hκ : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ,
      Kernel.compProd_of_not_isSFiniteKernel_left _ _ hκ, FunLike.coe_zero]
  ext s hs
  rw [Measure.bind_apply hs η.aemeasurable]; rw [Measure.snd_apply hs]; rw [Measure.bind_apply _ (Kernel.aemeasurable _)]; rw [Measure.lintegral_compProd (η.measurable_coe hs)]
  swap; · exact measurable_snd hs
  congr with a
  rw [Kernel.compProd_apply]
  · rfl
  · exact measurable_snd hs

@[simp]
/--
lemma `prodMkLeft_comp_compProd` / 引理 `prodMkLeft_comp_compProd`

English:
lemma prodMkLeft_comp_compProd
  given: {η : Kernel β γ} [SFinite μ] [IsSFiniteKernel κ]
  proof: by
  rw [← snd_compProd μ κ]; rw [Kernel.prodMkLeft]; rw [snd]; rw [← deterministic_comp_eq_map measurable_snd]; rw [comp_assoc]; rw [Kernel.comp_deterministic_eq_comap]

中文:
引理 prodMkLeft_comp_compProd
  条件: {η : 核 β γ} [SFinite μ] [是SFiniteKernel κ]
  证明: by
  rw [← snd_compProd μ κ]; rw [Kernel.prodMkLeft]; rw [snd]; rw [← deterministic_comp_eq_map measurable_snd]; rw [comp_assoc]; rw [Kernel.comp_deterministic_eq_comap]

Depends on / 依赖: Kernel, Kernel.comp_deterministic_eq_comap, Kernel.prodMkLeft, comp_assoc, comp_deterministic_eq_comap, deterministic_comp_eq_map, measurable_snd, prodMkLeft, snd_compProd
-/
lemma prodMkLeft_comp_compProd {η : Kernel β γ} [SFinite μ] [IsSFiniteKernel κ] :
    (η.prodMkLeft α) ∘ₘ μ otimesₘ κ = η ∘ₘ κ ∘ₘ μ := by
  rw [← snd_compProd μ κ]; rw [Kernel.prodMkLeft]; rw [snd]; rw [← deterministic_comp_eq_map measurable_snd]; rw [comp_assoc]; rw [Kernel.comp_deterministic_eq_comap]

/--
lemma `compProd_deterministic` / 引理 `compProd_deterministic`

English:
lemma compProd_deterministic
  given: [SFinite μ] {f : α -> β} (hf : Measurable f)
  proof: by
  rw [compProd_eq_comp_prod]; rw [Kernel.id]; rw [Kernel.deterministic_prod_deterministic]; rw [deterministic_comp_eq_map]
  rfl

中文:
引理 compProd_deterministic
  条件: [SFinite μ] {f : α -> β} (hf : 可测 f)
  证明: by
  rw [compProd_eq_comp_prod]; rw [Kernel.id]; rw [Kernel.deterministic_prod_deterministic]; rw [deterministic_comp_eq_map]
  rfl

Depends on / 依赖: Kernel, Kernel.deterministic_prod_deterministic, Kernel.id, compProd_eq_comp_prod, deterministic_comp_eq_map, deterministic_prod_deterministic
-/
lemma compProd_deterministic [SFinite μ] {f : α -> β} (hf : Measurable f) :
    μ otimesₘ Kernel.deterministic f hf = μ.map (fun a => (a, f a)) := by
  rw [compProd_eq_comp_prod]; rw [Kernel.id]; rw [Kernel.deterministic_prod_deterministic]; rw [deterministic_comp_eq_map]
  rfl

end CompProd

section AddSMul

@[simp]
/--
lemma `comp_add` / 引理 `comp_add`

English:
lemma comp_add
  statement: κ ∘ₘ (μ + ν) = κ ∘ₘ μ + κ ∘ₘ ν
  proof: by
  simp_rw [comp_eq_comp_const_apply, Kernel.const_add, Kernel.comp_add_right, _root_.add_apply]

中文:
引理 comp_add
  结论: κ ∘ₘ (μ + ν) = κ ∘ₘ μ + κ ∘ₘ ν
  证明: by
  simp_rw [comp_eq_comp_const_apply, Kernel.const_add, Kernel.comp_add_right, _root_.add_apply]

Depends on / 依赖: Kernel, Kernel.comp_add_right, Kernel.const_add, _root_, _root_.add_apply, add_apply, comp_add_right, comp_eq_comp_const_apply, const_add, simp_rw
-/
lemma comp_add : κ ∘ₘ (μ + ν) = κ ∘ₘ μ + κ ∘ₘ ν := by
  simp_rw [comp_eq_comp_const_apply, Kernel.const_add, Kernel.comp_add_right, _root_.add_apply]

/--
lemma `add_comp` / 引理 `add_comp`

English:
lemma add_comp
  statement: (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ
  proof: by
  simp_rw [comp_eq_comp_const_apply, Kernel.comp_add_left, _root_.add_apply]

中文:
引理 add_comp
  结论: (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ
  证明: by
  simp_rw [comp_eq_comp_const_apply, Kernel.comp_add_left, _root_.add_apply]

Depends on / 依赖: Kernel, Kernel.comp_add_left, _root_, _root_.add_apply, add_apply, comp_add_left, comp_eq_comp_const_apply, simp_rw
-/
lemma add_comp : (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by
  simp_rw [comp_eq_comp_const_apply, Kernel.comp_add_left, _root_.add_apply]

/-- Same as `add_comp` except that it uses `⇑κ + ⇑η` instead of `⇑(κ + η)` in order to have
a simp-normal form on the left of the equality. -/
@[simp]
/--
lemma `add_comp'` / 引理 `add_comp'`

English:
lemma add_comp'
  statement: (⇑κ + ⇑η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ
  proof: by rw [← FunLike.coe_add, add_comp]

@[simp]

中文:
引理 add_comp'
  结论: (⇑κ + ⇑η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ
  证明: by rw [← FunLike.coe_add, add_comp]

@[simp]

Depends on / 依赖: FunLike, FunLike.coe_add, add_comp, coe_add
-/
lemma add_comp' : (⇑κ + ⇑η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by rw [← FunLike.coe_add, add_comp]

@[simp]
/--
lemma `comp_smul` / 引理 `comp_smul`

English:
lemma comp_smul
  given: (a : Real>=0∞)
  statement: κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ)
  proof: by
  ext s hs
  simp only [bind_apply hs κ.aemeasurable, lintegral_smul_measure, smul_apply, smul_eq_mul]

中文:
引理 comp_smul
  条件: (a : 实数>=0∞)
  结论: κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ)
  证明: by
  ext s hs
  simp only [bind_apply hs κ.aemeasurable, lintegral_smul_measure, smul_apply, smul_eq_mul]

Depends on / 依赖: aemeasurable, bind_apply, lintegral_smul_measure, smul_apply, smul_eq_mul
-/
lemma comp_smul (a : Real>=0∞) : κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ) := by
  ext s hs
  simp only [bind_apply hs κ.aemeasurable, lintegral_smul_measure, smul_apply, smul_eq_mul]

end AddSMul

section AbsolutelyContinuous

/--
lemma `AbsolutelyContinuous.comp_right` / 引理 `AbsolutelyContinuous.comp_right`

English:
lemma AbsolutelyContinuous.comp_right
  given: (hμν : μ ≪ ν) (κ : Kernel α γ)
  proof: by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]; rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  exact hμν.ae_eq hs_zero

中文:
引理 AbsolutelyContinuous.comp_right
  条件: (hμν : μ ≪ ν) (κ : 核 α γ)
  证明: by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]; rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  exact hμν.ae_eq hs_zero

Depends on / 依赖: AbsolutelyContinuous, Kernel, Kernel.aemeasurable, Kernel.measurable_coe, Measure, Measure.AbsolutelyContinuous.mk, Measure.bind_apply, ae_eq, aemeasurable, bind_apply, hs_zero, lintegral_eq_zero_iff, measurable_coe
-/
lemma AbsolutelyContinuous.comp_right (hμν : μ ≪ ν) (κ : Kernel α γ) :
    κ ∘ₘ μ ≪ κ ∘ₘ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]; rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  exact hμν.ae_eq hs_zero

/--
lemma `AbsolutelyContinuous.comp_left` / 引理 `AbsolutelyContinuous.comp_left`

English:
lemma AbsolutelyContinuous.comp_left
  given: (μ : Measure α) (hκη : forallᵐ a ∂μ, κ a ≪ η a)
  proof: by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]; rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero

中文:
引理 AbsolutelyContinuous.comp_left
  条件: (μ : 测度 α) (hκη : 对任意ᵐ a ∂μ, κ a ≪ η a)
  证明: by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]; rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero

Depends on / 依赖: AbsolutelyContinuous, Kernel, Kernel.aemeasurable, Kernel.measurable_coe, Measure, Measure.AbsolutelyContinuous.mk, Measure.bind_apply, aemeasurable, bind_apply, filter_upwards, ha_ac, ha_zero, hs_zero, lintegral_eq_zero_iff, measurable_coe
-/
lemma AbsolutelyContinuous.comp_left (μ : Measure α) (hκη : forallᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ μ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]; rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero

/--
lemma `AbsolutelyContinuous.comp` / 引理 `AbsolutelyContinuous.comp`

English:
lemma AbsolutelyContinuous.comp
  given: (hμν : μ ≪ ν) (hκη : forallᵐ a ∂μ, κ a ≪ η a)
  proof: (AbsolutelyContinuous.comp_left μ hκη).trans (hμν.comp_right η)

中文:
引理 AbsolutelyContinuous.comp
  条件: (hμν : μ ≪ ν) (hκη : 对任意ᵐ a ∂μ, κ a ≪ η a)
  证明: (AbsolutelyContinuous.comp_left μ hκη).trans (hμν.comp_right η)

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.comp_left, comp_left, comp_right
-/
lemma AbsolutelyContinuous.comp (hμν : μ ≪ ν) (hκη : forallᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ ν :=
  (AbsolutelyContinuous.comp_left μ hκη).trans (hμν.comp_right η)

/--
lemma `absolutelyContinuous_comp_of_countable` / 引理 `absolutelyContinuous_comp_of_countable`

English:
lemma absolutelyContinuous_comp_of_countable
  given: [Countable α] [MeasurableSingletonClass α]
  proof: by
  rw [Measure.comp_eq_sum_of_countable]; rw [ae_iff_of_countable]
  exact fun ω hμω => Measure.absolutelyContinuous_sum_right ω (Measure.absolutelyContinuous_smul hμω)

中文:
引理 absolutelyContinuous_comp_of_countable
  条件: [可数 α] [MeasurableSingleton类 α]
  证明: by
  rw [Measure.comp_eq_sum_of_countable]; rw [ae_iff_of_countable]
  exact fun ω hμω => Measure.absolutelyContinuous_sum_right ω (Measure.absolutelyContinuous_smul hμω)

Depends on / 依赖: Measure, Measure.absolutelyContinuous_smul, Measure.absolutelyContinuous_sum_right, Measure.comp_eq_sum_of_countable, absolutelyContinuous_smul, absolutelyContinuous_sum_right, ae_iff_of_countable, comp_eq_sum_of_countable
-/
lemma absolutelyContinuous_comp_of_countable [Countable α] [MeasurableSingletonClass α] :
    forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  rw [Measure.comp_eq_sum_of_countable]; rw [ae_iff_of_countable]
  exact fun ω hμω => Measure.absolutelyContinuous_sum_right ω (Measure.absolutelyContinuous_smul hμω)

end AbsolutelyContinuous

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

section BoolKernel

variable {π : Measure Bool}

@[simp]
/--
lemma `Kernel.comp_boolKernel` / 引理 `Kernel.comp_boolKernel`

English:
lemma Kernel.comp_boolKernel
  given: (κ : Kernel α β) (μ ν : Measure α)
  proof: by
  ext b : 1
  rw [comp_apply]
  cases b <;> simp

中文:
引理 核.comp_boolKernel
  条件: (κ : 核 α β) (μ ν : 测度 α)
  证明: by
  ext b : 1
  rw [comp_apply]
  cases b <;> simp

Depends on / 依赖: comp_apply
-/
lemma Kernel.comp_boolKernel (κ : Kernel α β) (μ ν : Measure α) :
    κ ∘ₖ (boolKernel μ ν) = boolKernel (κ ∘ₘ μ) (κ ∘ₘ ν) := by
  ext b : 1
  rw [comp_apply]
  cases b <;> simp

/--
lemma `boolKernel_comp_measure` / 引理 `boolKernel_comp_measure`

English:
lemma boolKernel_comp_measure
  given: (μ ν : Measure α) (π : Measure Bool)
  proof: by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp [lintegral_fintype, mul_comm]

中文:
引理 boolKernel_comp_measure
  条件: (μ ν : 测度 α) (π : 测度 布尔值)
  证明: by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp [lintegral_fintype, mul_comm]

Depends on / 依赖: Kernel, Kernel.aemeasurable, Measure, Measure.bind_apply, aemeasurable, bind_apply, lintegral_fintype, mul_comm
-/
lemma boolKernel_comp_measure (μ ν : Measure α) (π : Measure Bool) :
    Kernel.boolKernel μ ν ∘ₘ π = π {true} • ν + π {false} • μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp [lintegral_fintype, mul_comm]

/--
lemma `absolutelyContinuous_boolKernel_comp_left` / 引理 `absolutelyContinuous_boolKernel_comp_left`

English:
lemma absolutelyContinuous_boolKernel_comp_left
  given: (μ ν : Measure α) (hπ : π {false} != 0)
  proof: boolKernel_comp_measure _ _ _ ▸ add_comm _ (π {true} • ν) ▸
    (Measure.absolutelyContinuous_smul hπ).add_right _

中文:
引理 absolutelyContinuous_boolKernel_comp_left
  条件: (μ ν : 测度 α) (hπ : π {false} != 0)
  证明: boolKernel_comp_measure _ _ _ ▸ add_comm _ (π {true} • ν) ▸
    (Measure.absolutelyContinuous_smul hπ).add_right _

Depends on / 依赖: Measure, Measure.absolutelyContinuous_smul, absolutelyContinuous_smul, add_comm, add_right, boolKernel_comp_measure
-/
lemma absolutelyContinuous_boolKernel_comp_left (μ ν : Measure α) (hπ : π {false} != 0) :
    μ ≪ Kernel.boolKernel μ ν ∘ₘ π :=
  boolKernel_comp_measure _ _ _ ▸ add_comm _ (π {true} • ν) ▸
    (Measure.absolutelyContinuous_smul hπ).add_right _

/--
lemma `absolutelyContinuous_boolKernel_comp_right` / 引理 `absolutelyContinuous_boolKernel_comp_right`

English:
lemma absolutelyContinuous_boolKernel_comp_right
  given: (μ ν : Measure α) (hπ : π {true} != 0)
  proof: boolKernel_comp_measure _ _ _ ▸ (Measure.absolutelyContinuous_smul hπ).add_right _

中文:
引理 absolutelyContinuous_boolKernel_comp_right
  条件: (μ ν : 测度 α) (hπ : π {true} != 0)
  证明: boolKernel_comp_measure _ _ _ ▸ (Measure.absolutelyContinuous_smul hπ).add_right _

Depends on / 依赖: Measure, Measure.absolutelyContinuous_smul, absolutelyContinuous_smul, add_right, boolKernel_comp_measure
-/
lemma absolutelyContinuous_boolKernel_comp_right (μ ν : Measure α) (hπ : π {true} != 0) :
    ν ≪ Kernel.boolKernel μ ν ∘ₘ π :=
  boolKernel_comp_measure _ _ _ ▸ (Measure.absolutelyContinuous_smul hπ).add_right _

end BoolKernel

end ProbabilityTheory
