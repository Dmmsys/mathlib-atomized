/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# Condition for two kernels to be equal almost everywhere

We prove that two finite kernels `κ, η : Kernel α β` are `μ`-a.e. equal for a finite measure `μ` iff
the composition-products `μ ⊗ₘ κ` and `μ ⊗ₘ η` are equal.
The result requires `α` to be countable or `β` to be a countably generated measurable space.

## Main statements

* `compProd_withDensity`: `μ ⊗ₘ (κ.withDensity f) = (μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2)`
* `compProd_eq_iff`: `μ ⊗ₘ κ = μ ⊗ₘ η ↔ κ =ᵐ[μ] η`

-/

public section

open ProbabilityTheory MeasureTheory

open scoped ENNReal

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β}
  {f : α -> β -> Real>=0∞}

namespace MeasureTheory.Measure

/--
lemma `compProd_withDensity` / 引理 `compProd_withDensity`

English:
lemma compProd_withDensity
  statement: [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel (κ.withDensity f)]
  proof: by
  ext s hs
  rw [compProd_apply hs]; rw [withDensity_apply _ hs]; rw [← lintegral_indicator hs]; rw [lintegral_compProd]
  · congr with a
    rw [Kernel.withDensity_apply' _ hf]; rw [← lintegral_indicator (measurable_prodMk_left hs)]
    rfl
  · exact hf.indicator hs

中文:
引理 compProd_withDensity
  结论: [SFinite μ] [是SFiniteKernel κ] [是SFiniteKernel (κ.withDensity f)]
  证明: by
  ext s hs
  rw [compProd_apply hs]; rw [withDensity_apply _ hs]; rw [← lintegral_indicator hs]; rw [lintegral_compProd]
  · congr with a
    rw [Kernel.withDensity_apply' _ hf]; rw [← lintegral_indicator (measurable_prodMk_left hs)]
    rfl
  · exact hf.indicator hs

Depends on / 依赖: Kernel, Kernel.withDensity_apply, compProd_apply, hf.indicator, indicator, lintegral_compProd, lintegral_indicator, measurable_prodMk_left, withDensity_apply
-/
lemma compProd_withDensity [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel (κ.withDensity f)]
    (hf : Measurable (Function.uncurry f)) :
    μ otimesₘ (κ.withDensity f) = (μ otimesₘ κ).withDensity (fun p => f p.1 p.2) := by
  ext s hs
  rw [compProd_apply hs]; rw [withDensity_apply _ hs]; rw [← lintegral_indicator hs]; rw [lintegral_compProd]
  · congr with a
    rw [Kernel.withDensity_apply' _ hf]; rw [← lintegral_indicator (measurable_prodMk_left hs)]
    rfl
  · exact hf.indicator hs

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {η : Kernel α β} [MeasurableSpace.CountableOrCountablyGenerated α β]

/--
lemma `ae_eq_of_compProd_eq` / 引理 `ae_eq_of_compProd_eq`

English:
lemma ae_eq_of_compProd_eq
  statement: [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  have h_ac : forallᵐ a ∂μ, κ a ≪ η a := (Measure.absolutelyContinuous_of_eq h).kernel_of_compProd
  have hκ_eq : forallᵐ a ∂μ, κ a = η.withDensity (κ.rnDeriv η) a := by
    filter_upwards [h_ac] with a ha using (Kernel.withDensity_rnDeriv_eq ha).symm
  suffices forallᵐ a ∂μ, forallᵐ b ∂(η a), κ.rnDeriv η a b = 1 by
    filter_upwards [h_ac, this] with a h_ac h using (rnDeriv_eq_one_iff_eq h_ac).mp h
  refine Measure.ae_ae_of_ae_compProd (p := fun x => κ.rnDeriv η x.1 x.2 = 1) ?_
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ => ?_
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
    Set.univ_inter, one_mul]
  calc ∫⁻ x in s, κ.rnDeriv η x.1 x.2 ∂μ otimesₘ η
  _ = (μ otimesₘ κ) s := by
    rw [Measure.compProd_congr hκ_eq]; rw [Measure.compProd_withDensity]; rw [withDensity_apply _ hs]
    fun_prop
  _ = (μ otimesₘ η) s := by rw [h]

中文:
引理 ae_eq_of_compProd_eq
  结论: [是有限测度 μ] [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  have h_ac : forallᵐ a ∂μ, κ a ≪ η a := (Measure.absolutelyContinuous_of_eq h).kernel_of_compProd
  have hκ_eq : forallᵐ a ∂μ, κ a = η.withDensity (κ.rnDeriv η) a := by
    filter_upwards [h_ac] with a ha using (Kernel.withDensity_rnDeriv_eq ha).symm
  suffices forallᵐ a ∂μ, forallᵐ b ∂(η a), κ.rnDeriv η a b = 1 by
    filter_upwards [h_ac, this] with a h_ac h using (rnDeriv_eq_one_iff_eq h_ac).mp h
  refine Measure.ae_ae_of_ae_compProd (p := fun x => κ.rnDeriv η x.1 x.2 = 1) ?_
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ => ?_
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
    Set.univ_inter, one_mul]
  calc ∫⁻ x in s, κ.rnDeriv η x.1 x.2 ∂μ otimesₘ η
  _ = (μ otimesₘ κ) s := by
    rw [Measure.compProd_congr hκ_eq]; rw [Measure.compProd_withDensity]; rw [withDensity_apply _ hs]
    fun_prop
  _ = (μ otimesₘ η) s := by rw [h]

Depends on / 依赖: Kernel, Kernel.withDensity_rnDeriv_eq, Measure, Measure.absolutelyContinuous_of_eq, Measure.ae_ae_of_ae_compProd, absolutelyContinuous_of_eq, ae_ae_of_ae_compProd, ae_eq_of_forall_setLI, filter_upwards, h_ac, kernel_of_compProd, rnDeriv, rnDeriv_eq_one_iff_eq, withDensity, withDensity_rnDeriv_eq
-/
lemma ae_eq_of_compProd_eq [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : μ otimesₘ κ = μ otimesₘ η) :
    κ =ᵐ[μ] η := by
  have h_ac : forallᵐ a ∂μ, κ a ≪ η a := (Measure.absolutelyContinuous_of_eq h).kernel_of_compProd
  have hκ_eq : forallᵐ a ∂μ, κ a = η.withDensity (κ.rnDeriv η) a := by
    filter_upwards [h_ac] with a ha using (Kernel.withDensity_rnDeriv_eq ha).symm
  suffices forallᵐ a ∂μ, forallᵐ b ∂(η a), κ.rnDeriv η a b = 1 by
    filter_upwards [h_ac, this] with a h_ac h using (rnDeriv_eq_one_iff_eq h_ac).mp h
  refine Measure.ae_ae_of_ae_compProd (p := fun x => κ.rnDeriv η x.1 x.2 = 1) ?_
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ => ?_
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
    Set.univ_inter, one_mul]
  calc ∫⁻ x in s, κ.rnDeriv η x.1 x.2 ∂μ otimesₘ η
  _ = (μ otimesₘ κ) s := by
    rw [Measure.compProd_congr hκ_eq]; rw [Measure.compProd_withDensity]; rw [withDensity_apply _ hs]
    fun_prop
  _ = (μ otimesₘ η) s := by rw [h]

/--
lemma `compProd_eq_iff` / 引理 `compProd_eq_iff`

English:
lemma compProd_eq_iff
  given: [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: ⟨Kernel.ae_eq_of_compProd_eq, Measure.compProd_congr⟩

中文:
引理 compProd_eq_iff
  条件: [是有限测度 μ] [是FiniteKernel κ] [是FiniteKernel η]
  证明: ⟨Kernel.ae_eq_of_compProd_eq, Measure.compProd_congr⟩

Depends on / 依赖: Kernel, Kernel.ae_eq_of_compProd_eq, Measure, Measure.compProd_congr, ae_eq_of_compProd_eq, compProd_congr
-/
lemma compProd_eq_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ otimesₘ κ = μ otimesₘ η ↔ κ =ᵐ[μ] η :=
  ⟨Kernel.ae_eq_of_compProd_eq, Measure.compProd_congr⟩

end ProbabilityTheory.Kernel
