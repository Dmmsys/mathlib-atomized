/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Absolute continuity of the composition of measures and kernels

This file contains some results about the absolute continuity of the composition of measures and
kernels which use an assumption `CountableOrCountablyGenerated α β` on the measurable spaces.

Results that hold without that assumption are in files about the definitions of compositions and
products, like `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` and
`Mathlib/Probability/Kernel/Composition/MeasureComp.lean`.

The assumption ensures the measurability of the sets where two kernels are absolutely continuous
or mutually singular.

## Main statements

* `absolutelyContinuous_compProd_iff'`: `μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a`.

-/

public section

open ProbabilityTheory Filter

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} [IsFiniteKernel κ] [IsFiniteKernel η]
  [MeasurableSpace.CountableOrCountablyGenerated α β]

/--
lemma `MutuallySingular.compProd_of_right` / 引理 `MutuallySingular.compProd_of_right`

English:
lemma MutuallySingular.compProd_of_right
  given: (μ ν : Measure α) (hκη : forallᵐ a ∂μ, κ a ⟂ₘ η a)
  proof: by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  let s := κ.mutuallySingularSet η
  have hs : MeasurableSet s := Kernel.measurableSet_mutuallySingularSet κ η
  symm
  refine ⟨s, hs, ?_⟩
  rw [compProd_apply hs]; rw [compProd_apply hs.compl]
  have h_eq a : Prod.mk a ⁻¹' s = Kernel.mutuallySingularSetSlice κ η a := rfl
  have h1 a : η a (Prod.mk a ⁻¹' s) = 0 := by rw [h_eq, Kernel.measure_mutuallySingularSetSlice]
  have h2 : forallᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s)ᶜ = 0 := by
    filter_upwards [hκη] with a ha
    rwa [h_eq, ← Kernel.withDensity_rnDeriv_eq_zero_iff_measure_eq_zero κ η a,
      Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingular]
  simp [h1, lintegral_congr_ae h2]

中文:
引理 互奇异.compProd_of_right
  条件: (μ ν : 测度 α) (hκη : 对任意ᵐ a ∂μ, κ a ⟂ₘ η a)
  证明: by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  let s := κ.mutuallySingularSet η
  have hs : MeasurableSet s := Kernel.measurableSet_mutuallySingularSet κ η
  symm
  refine ⟨s, hs, ?_⟩
  rw [compProd_apply hs]; rw [compProd_apply hs.compl]
  have h_eq a : Prod.mk a ⁻¹' s = Kernel.mutuallySingularSetSlice κ η a := rfl
  have h1 a : η a (Prod.mk a ⁻¹' s) = 0 := by rw [h_eq, Kernel.measure_mutuallySingularSetSlice]
  have h2 : forallᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s)ᶜ = 0 := by
    filter_upwards [hκη] with a ha
    rwa [h_eq, ← Kernel.withDensity_rnDeriv_eq_zero_iff_measure_eq_zero κ η a,
      Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingular]
  simp [h1, lintegral_congr_ae h2]

Depends on / 依赖: Kernel, Kernel.measurableSet_mutuallySingularSet, Kernel.measure_mutuallySingularSet, Kernel.mutuallySingularSetSlice, MeasurableSet, Prod.mk, SFinite, compProd_apply, compProd_of_not_sfinite, h_eq, hs.compl, measurableSet_mutuallySingularSet, measure_mutuallySingularSet, mutuallySingularSet, mutuallySingularSetSlice
-/
lemma MutuallySingular.compProd_of_right (μ ν : Measure α) (hκη : forallᵐ a ∂μ, κ a ⟂ₘ η a) :
    μ otimesₘ κ ⟂ₘ ν otimesₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  let s := κ.mutuallySingularSet η
  have hs : MeasurableSet s := Kernel.measurableSet_mutuallySingularSet κ η
  symm
  refine ⟨s, hs, ?_⟩
  rw [compProd_apply hs]; rw [compProd_apply hs.compl]
  have h_eq a : Prod.mk a ⁻¹' s = Kernel.mutuallySingularSetSlice κ η a := rfl
  have h1 a : η a (Prod.mk a ⁻¹' s) = 0 := by rw [h_eq, Kernel.measure_mutuallySingularSetSlice]
  have h2 : forallᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s)ᶜ = 0 := by
    filter_upwards [hκη] with a ha
    rwa [h_eq, ← Kernel.withDensity_rnDeriv_eq_zero_iff_measure_eq_zero κ η a,
      Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingular]
  simp [h1, lintegral_congr_ae h2]

/--
lemma `MutuallySingular.compProd_of_right'` / 引理 `MutuallySingular.compProd_of_right'`

English:
lemma MutuallySingular.compProd_of_right'
  given: (μ ν : Measure α) (hκη : forallᵐ a ∂ν, κ a ⟂ₘ η a)
  proof: by
  refine (MutuallySingular.compProd_of_right _ _ ?_).symm
  simp_rw [MutuallySingular.comm, hκη]

中文:
引理 互奇异.compProd_of_right'
  条件: (μ ν : 测度 α) (hκη : 对任意ᵐ a ∂ν, κ a ⟂ₘ η a)
  证明: by
  refine (MutuallySingular.compProd_of_right _ _ ?_).symm
  simp_rw [MutuallySingular.comm, hκη]

Depends on / 依赖: MutuallySingular, MutuallySingular.comm, MutuallySingular.compProd_of_right, compProd_of_right, simp_rw
-/
lemma MutuallySingular.compProd_of_right' (μ ν : Measure α) (hκη : forallᵐ a ∂ν, κ a ⟂ₘ η a) :
    μ otimesₘ κ ⟂ₘ ν otimesₘ η := by
  refine (MutuallySingular.compProd_of_right _ _ ?_).symm
  simp_rw [MutuallySingular.comm, hκη]

/--
lemma `mutuallySingular_compProd_right_iff` / 引理 `mutuallySingular_compProd_right_iff`

English:
lemma mutuallySingular_compProd_right_iff
  given: [SFinite μ]
  proof: ⟨fun h => mutuallySingular_of_mutuallySingular_compProd h AbsolutelyContinuous.rfl
    AbsolutelyContinuous.rfl, MutuallySingular.compProd_of_right _ _⟩

中文:
引理 mutuallySingular_compProd_right_iff
  条件: [SFinite μ]
  证明: ⟨fun h => mutuallySingular_of_mutuallySingular_compProd h AbsolutelyContinuous.rfl
    AbsolutelyContinuous.rfl, MutuallySingular.compProd_of_right _ _⟩

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl, MutuallySingular, MutuallySingular.compProd_of_right, compProd_of_right, mutuallySingular_of_mutuallySingular_compProd
-/
lemma mutuallySingular_compProd_right_iff [SFinite μ] :
    μ otimesₘ κ ⟂ₘ μ otimesₘ η ↔ forallᵐ a ∂μ, κ a ⟂ₘ η a :=
  ⟨fun h => mutuallySingular_of_mutuallySingular_compProd h AbsolutelyContinuous.rfl
    AbsolutelyContinuous.rfl, MutuallySingular.compProd_of_right _ _⟩

/--
lemma `AbsolutelyContinuous.kernel_of_compProd` / 引理 `AbsolutelyContinuous.kernel_of_compProd`

English:
lemma AbsolutelyContinuous.kernel_of_compProd
  given: [SFinite μ] (h : μ otimesₘ κ ≪ ν otimesₘ η)
  proof: by
  suffices forallᵐ a ∂μ, κ.singularPart η a = 0 by
    filter_upwards [this] with a ha
    rwa [Kernel.singularPart_eq_zero_iff_absolutelyContinuous] at ha
  rw [← κ.rnDeriv_add_singularPart η]; rw [compProd_add_right]; rw [AbsolutelyContinuous.add_left_iff] at h
  have : μ otimesₘ κ.singularPart η ⟂ₘ ν otimesₘ η :=
    MutuallySingular.compProd_of_right μ ν (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  refine compProd_eq_zero_iff.mp ?_
  exact eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2 this

中文:
引理 AbsolutelyContinuous.kernel_of_compProd
  条件: [SFinite μ] (h : μ otimesₘ κ ≪ ν otimesₘ η)
  证明: by
  suffices forallᵐ a ∂μ, κ.singularPart η a = 0 by
    filter_upwards [this] with a ha
    rwa [Kernel.singularPart_eq_zero_iff_absolutelyContinuous] at ha
  rw [← κ.rnDeriv_add_singularPart η]; rw [compProd_add_right]; rw [AbsolutelyContinuous.add_left_iff] at h
  have : μ otimesₘ κ.singularPart η ⟂ₘ ν otimesₘ η :=
    MutuallySingular.compProd_of_right μ ν (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  refine compProd_eq_zero_iff.mp ?_
  exact eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2 this

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.add_left_iff, Kernel, Kernel.mutuallySingular_singularPart, Kernel.singularPart_eq_zero_iff_absolutelyContinuous, MutuallySingular, MutuallySingular.compProd_of_right, add_left_iff, compProd_add_right, compProd_eq_zero_iff, compProd_eq_zero_iff.mp, compProd_of_right, eq_zero_of_absolutelyContinuous_of_mutuallySingular, filter_upwards, mutuallySingular_singularPart, of_forall, rnDeriv_add_singularPart, singularPart, singularPart_eq_zero_iff_absolutelyContinuous
-/
lemma AbsolutelyContinuous.kernel_of_compProd [SFinite μ] (h : μ otimesₘ κ ≪ ν otimesₘ η) :
    forallᵐ a ∂μ, κ a ≪ η a := by
  suffices forallᵐ a ∂μ, κ.singularPart η a = 0 by
    filter_upwards [this] with a ha
    rwa [Kernel.singularPart_eq_zero_iff_absolutelyContinuous] at ha
  rw [← κ.rnDeriv_add_singularPart η]; rw [compProd_add_right]; rw [AbsolutelyContinuous.add_left_iff] at h
  have : μ otimesₘ κ.singularPart η ⟂ₘ ν otimesₘ η :=
    MutuallySingular.compProd_of_right μ ν (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  refine compProd_eq_zero_iff.mp ?_
  exact eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2 this

/--
lemma `absolutelyContinuous_compProd_iff'` / 引理 `absolutelyContinuous_compProd_iff'`

English:
lemma absolutelyContinuous_compProd_iff'
  given: [SFinite μ] [SFinite ν] [forall a, NeZero (κ a)]
  proof: ⟨fun h => ⟨absolutelyContinuous_of_compProd h, h.kernel_of_compProd⟩, fun h => h.1.compProd h.2⟩

中文:
引理 absolutelyContinuous_compProd_iff'
  条件: [SFinite μ] [SFinite ν] [对任意 a, NeZero (κ a)]
  证明: ⟨fun h => ⟨absolutelyContinuous_of_compProd h, h.kernel_of_compProd⟩, fun h => h.1.compProd h.2⟩

Depends on / 依赖: absolutelyContinuous_of_compProd, compProd, h.kernel_of_compProd, kernel_of_compProd
-/
lemma absolutelyContinuous_compProd_iff' [SFinite μ] [SFinite ν] [forall a, NeZero (κ a)] :
    μ otimesₘ κ ≪ ν otimesₘ η ↔ μ ≪ ν ∧ forallᵐ a ∂μ, κ a ≪ η a :=
  ⟨fun h => ⟨absolutelyContinuous_of_compProd h, h.kernel_of_compProd⟩, fun h => h.1.compProd h.2⟩

/--
lemma `absolutelyContinuous_compProd_right_iff` / 引理 `absolutelyContinuous_compProd_right_iff`

English:
lemma absolutelyContinuous_compProd_right_iff
  given: [SFinite μ]
  proof: ⟨AbsolutelyContinuous.kernel_of_compProd, AbsolutelyContinuous.compProd_right⟩

中文:
引理 absolutelyContinuous_compProd_right_iff
  条件: [SFinite μ]
  证明: ⟨AbsolutelyContinuous.kernel_of_compProd, AbsolutelyContinuous.compProd_right⟩

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.compProd_right, AbsolutelyContinuous.kernel_of_compProd, compProd_right, kernel_of_compProd
-/
lemma absolutelyContinuous_compProd_right_iff [SFinite μ] :
    μ otimesₘ κ ≪ μ otimesₘ η ↔ forallᵐ a ∂μ, κ a ≪ η a :=
  ⟨AbsolutelyContinuous.kernel_of_compProd, AbsolutelyContinuous.compProd_right⟩

end MeasureTheory.Measure
