/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.ContinuousMap.ContinuousMapZero
public import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap

/-!
# Specific results about `ContinuousMapZero`-valued integration

In this file, we collect a few results regarding integrability, on a measure space `(X, μ)`,
of a `C(Y, E)₀`-valued function, where `Y` is a compact topological space with a distinguished `0`,
and `E` is a normed group.

The structure of this file is largely similar to that of
`Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap`, which contains a more detailed
module docstring.

-/

public section

open MeasureTheory

namespace ContinuousMapZero

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E]

/--
lemma `hasFiniteIntegral_of_bound` / 引理 `hasFiniteIntegral_of_bound`

English:
lemma hasFiniteIntegral_of_bound
  statement: [CompactSpace Y] [Zero Y] (f : X -> C(Y, E)₀) (bound : X -> Real)
  proof: by
  have bound_nonneg : 0 <=ᵐ[μ] bound := by
    filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x 0)
  refine .mono' bound_int ?_
  filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
.mpr bound_ge_x exact ContinuousMap.norm_le _ bound_nonneg_x

中文:
引理 hasFiniteIntegral_of_bound
  结论: [CompactSpace Y] [Zero Y] (f : X -> C(Y, E)₀) (bound : X -> 实数)
  证明: by
  have bound_nonneg : 0 <=ᵐ[μ] bound := by
    filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x 0)
  refine .mono' bound_int ?_
  filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
.mpr bound_ge_x exact ContinuousMap.norm_le _ bound_nonneg_x

Depends on / 依赖: ContinuousMap, ContinuousMap.norm_le, bound_ge, bound_ge_x, bound_int, bound_nonneg, bound_nonneg_x, bound_x, filter_upwards, le_trans, norm_le, norm_nonneg
-/
lemma hasFiniteIntegral_of_bound [CompactSpace Y] [Zero Y] (f : X -> C(Y, E)₀) (bound : X -> Real)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : forallᵐ x ∂μ, forall y : Y, ‖f x y‖ <= bound x) :
    HasFiniteIntegral f μ := by
  have bound_nonneg : 0 <=ᵐ[μ] bound := by
    filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x 0)
  refine .mono' bound_int ?_
  filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
.mpr bound_ge_x exact ContinuousMap.norm_le _ bound_nonneg_x

/--
lemma `hasFiniteIntegral_mkD_of_bound` / 引理 `hasFiniteIntegral_mkD_of_bound`

English:
lemma hasFiniteIntegral_mkD_of_bound
  statement: [CompactSpace Y] [Zero Y] (f : X -> Y -> E) (g : C(Y, E)₀)
  proof: by
  refine hasFiniteIntegral_of_bound _ bound bound_int ?_
  filter_upwards [bound_ge, f_ae_cont, f_ae_zero] with x bound_ge_x cont_x zero_x
  simpa only [mkD_apply_of_continuous cont_x zero_x] using bound_ge_x

中文:
引理 hasFiniteIntegral_mkD_of_bound
  结论: [CompactSpace Y] [Zero Y] (f : X -> Y -> E) (g : C(Y, E)₀)
  证明: by
  refine hasFiniteIntegral_of_bound _ bound bound_int ?_
  filter_upwards [bound_ge, f_ae_cont, f_ae_zero] with x bound_ge_x cont_x zero_x
  simpa only [mkD_apply_of_continuous cont_x zero_x] using bound_ge_x

Depends on / 依赖: bound_ge, bound_ge_x, bound_int, cont_x, f_ae_cont, f_ae_zero, filter_upwards, hasFiniteIntegral_of_bound, mkD_apply_of_continuous, zero_x
-/
lemma hasFiniteIntegral_mkD_of_bound [CompactSpace Y] [Zero Y] (f : X -> Y -> E) (g : C(Y, E)₀)
    (f_ae_cont : forallᵐ x ∂μ, Continuous (f x))
    (f_ae_zero : forallᵐ x ∂μ, f x 0 = 0)
    (bound : X -> Real)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : forallᵐ x ∂μ, forall y : Y, ‖f x y‖ <= bound x) :
    HasFiniteIntegral (fun x => mkD (f x) g) μ := by
  refine hasFiniteIntegral_of_bound _ bound bound_int ?_
  filter_upwards [bound_ge, f_ae_cont, f_ae_zero] with x bound_ge_x cont_x zero_x
  simpa only [mkD_apply_of_continuous cont_x zero_x] using bound_ge_x

/--
lemma `hasFiniteIntegral_mkD_restrict_of_bound` / 引理 `hasFiniteIntegral_mkD_restrict_of_bound`

English:
lemma hasFiniteIntegral_mkD_restrict_of_bound
  statement: {s : Set Y} [CompactSpace s] [Zero s]
  proof: by
  refine hasFiniteIntegral_mkD_of_bound _ _ ?_ f_ae_zero bound bound_int ?_
  · simpa [← continuousOn_iff_continuous_domRestrict]
  · simpa

中文:
引理 hasFiniteIntegral_mkD_restrict_of_bound
  结论: {s : Set Y} [CompactSpace s] [Zero s]
  证明: by
  refine hasFiniteIntegral_mkD_of_bound _ _ ?_ f_ae_zero bound bound_int ?_
  · simpa [← continuousOn_iff_continuous_domRestrict]
  · simpa

Depends on / 依赖: bound_int, continuousOn_iff_continuous_domRestrict, f_ae_zero, hasFiniteIntegral_mkD_of_bound
-/
lemma hasFiniteIntegral_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] [Zero s]
    (f : X -> Y -> E) (g : C(s, E)₀)
    (f_ae_contOn : forallᵐ x ∂μ, ContinuousOn (f x) s)
    (f_ae_zero : forallᵐ x ∂μ, f x (0 : s) = 0)
    (bound : X -> Real)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : forallᵐ x ∂μ, forall y in s, ‖f x y‖ <= bound x) :
    HasFiniteIntegral (fun x => mkD (s.domRestrict (f x)) g) μ := by
  refine hasFiniteIntegral_mkD_of_bound _ _ ?_ f_ae_zero bound bound_int ?_
  · simpa [← continuousOn_iff_continuous_domRestrict]
  · simpa

/--
lemma `aeStronglyMeasurable_mkD_of_uncurry` / 引理 `aeStronglyMeasurable_mkD_of_uncurry`

English:
lemma aeStronglyMeasurable_mkD_of_uncurry
  statement: [CompactSpace Y] [Zero Y] [TopologicalSpace X]
  proof: by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_mkD_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

中文:
引理 aeStronglyMeasurable_mkD_of_uncurry
  结论: [CompactSpace Y] [Zero Y] [TopologicalSpace X]
  证明: by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_mkD_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

Depends on / 依赖: ContinuousMap, ContinuousMap.aeStronglyMeasurable_mkD_of_uncurry, ContinuousMapZero, ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff, aeStronglyMeasurable_mkD_of_uncurry, aestronglyMeasurable_comp_iff, aestronglyMeasurable_congr, f_cont, f_zero, filter_upwards, isEmbedding_toContinuousMap, mkD_eq_mkD_of_map_zero, zero_x
-/
lemma aeStronglyMeasurable_mkD_of_uncurry [CompactSpace Y] [Zero Y] [TopologicalSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (f : X -> Y -> E) (g : C(Y, E)₀) (f_cont : Continuous (Function.uncurry f))
    (f_zero : forallᵐ x ∂μ, f x 0 = 0) :
    AEStronglyMeasurable (fun x => mkD (f x) g) μ := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_mkD_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

open Set in
/--
lemma `aeStronglyMeasurable_restrict_mkD_of_uncurry` / 引理 `aeStronglyMeasurable_restrict_mkD_of_uncurry`

English:
lemma aeStronglyMeasurable_restrict_mkD_of_uncurry
  statement: [CompactSpace Y] [Zero Y] {s : Set X}
  proof: by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

中文:
引理 aeStronglyMeasurable_restrict_mkD_of_uncurry
  结论: [CompactSpace Y] [Zero Y] {s : Set X}
  证明: by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

Depends on / 依赖: ContinuousMap, ContinuousMap.aeStronglyMeasurable_restrict_mkD_of_uncurry, ContinuousMapZero, ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff, aeStronglyMeasurable_restrict_mkD_of_uncurry, aestronglyMeasurable_comp_iff, aestronglyMeasurable_congr, f_cont, f_zero, filter_upwards, isEmbedding_toContinuousMap, mkD_eq_mkD_of_map_zero, zero_x
-/
lemma aeStronglyMeasurable_restrict_mkD_of_uncurry [CompactSpace Y] [Zero Y] {s : Set X}
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (hs : MeasurableSet s) (f : X -> Y -> E) (g : C(Y, E)₀)
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ))
    (f_zero : forallᵐ x ∂(μ.restrict s), f x 0 = 0) :
    AEStronglyMeasurable (fun x => mkD (f x) g) (μ.restrict s) := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

open Set in
/--
lemma `aeStronglyMeasurable_mkD_restrict_of_uncurry` / 引理 `aeStronglyMeasurable_mkD_restrict_of_uncurry`

English:
lemma aeStronglyMeasurable_mkD_restrict_of_uncurry
  statement: {t : Set Y} [CompactSpace t] [Zero t]
  proof: by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

中文:
引理 aeStronglyMeasurable_mkD_restrict_of_uncurry
  结论: {t : Set Y} [CompactSpace t] [Zero t]
  证明: by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

Depends on / 依赖: ContinuousMap, ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry, ContinuousMapZero, ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff, aeStronglyMeasurable_mkD_restrict_of_uncurry, aestronglyMeasurable_comp_iff, aestronglyMeasurable_congr, f_cont, f_zero, filter_upwards, isEmbedding_toContinuousMap, mkD_eq_mkD_of_map_zero, zero_x
-/
lemma aeStronglyMeasurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [Zero t]
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(t, E))]
    (f : X -> Y -> E) (g : C(t, E)₀) (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t))
    (f_zero : forallᵐ x ∂μ, f x (0 : t) = 0) :
    AEStronglyMeasurable (fun x => mkD (t.domRestrict (f x)) g) μ := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

open Set in
/--
lemma `aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry` / 引理 `aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry`

English:
lemma aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry
  statement: {s : Set X} {t : Set Y}
  proof: by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

中文:
引理 aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry
  结论: {s : Set X} {t : Set Y}
  证明: by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

Depends on / 依赖: ContinuousMap, ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry, ContinuousMapZero, ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff, aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry, aestronglyMeasurable_comp_iff, aestronglyMeasurable_congr, f_cont, f_zero, filter_upwards, isEmbedding_toContinuousMap, mkD_eq_mkD_of_map_zero, zero_x
-/
lemma aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y}
    [CompactSpace t] [Zero t] [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X (C(t, E))]
    (hs : MeasurableSet s) (f : X -> Y -> E) (g : C(t, E)₀)
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t))
    (f_zero : forallᵐ x ∂(μ.restrict s), f x (0 : t) = 0) :
    AEStronglyMeasurable (fun x => mkD (t.domRestrict (f x)) g) (μ.restrict s) := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
.mp refine aestronglyMeasurable_congr ?_
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

end ContinuousMapZero
