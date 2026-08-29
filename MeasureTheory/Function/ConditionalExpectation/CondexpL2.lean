/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Conditional expectation in L2

This file contains one step of the construction of the conditional expectation, which is completed
in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`. See that file for a
description of the full process.

We build the conditional expectation of an `L²` function, as an element of `L²`. This is the
orthogonal projection on the subspace of almost everywhere `m`-measurable functions.

## Main definitions

* `condExpL2`: Conditional expectation of a function in L2 with respect to a sigma-algebra: it is
  the orthogonal projection on the subspace `lpMeas`.

## Implementation notes

Most of the results in this file are valid for a complete real normed space `F`.
However, some lemmas also use `𝕜 : RCLike`:
* `condExpL2` is defined only for an `InnerProductSpace` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `NormedSpace 𝕜 F`.

-/

@[expose] public section


open TopologicalSpace Filter ContinuousLinearMap

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α E E' F G G' 𝕜 : Type*} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- E for an inner product space
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
  -- E' for an inner product space on which we compute integrals
  [NormedAddCommGroup E']
  [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedSpace Real E']
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- G for a Lp add_subgroup
  [NormedAddCommGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedAddCommGroup G']
  [NormedSpace Real G'] [CompleteSpace G']

variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (E 𝕜)

/--
Definition of `condExpL2` / `condExpL2` 的定义

English:
definition condExpL2
  signature: (hm : m <= m0)
  body: haveI : Fact (m <= m0) := ⟨hm⟩
  (lpMeas E 𝕜 m 2 μ).orthogonalProjectionOnto

中文:
定义 condExpL2
  签名: (hm : m <= m0)
  定义体: haveI : Fact (m <= m0) := ⟨hm⟩
  (lpMeas E 𝕜 m 2 μ).orthogonalProjectionOnto

Depends on / 依赖: lpMeas, orthogonalProjectionOnto
-/
noncomputable def condExpL2 (hm : m <= m0) : (α ->₂[μ] E) ->L[𝕜] lpMeas E 𝕜 m 2 μ :=
  haveI : Fact (m <= m0) := ⟨hm⟩
  (lpMeas E 𝕜 m 2 μ).orthogonalProjectionOnto

variable {E 𝕜}

/--
theorem `aestronglyMeasurable_condExpL2` / 定理 `aestronglyMeasurable_condExpL2`

English:
theorem aestronglyMeasurable_condExpL2
  given: (hm : m <= m0) (f : α ->₂[μ] E)
  proof: lpMeas.aestronglyMeasurable _

中文:
定理 aestronglyMeasurable_condExpL2
  条件: (hm : m <= m0) (f : α ->₂[μ] E)
  证明: lpMeas.aestronglyMeasurable _

Depends on / 依赖: aestronglyMeasurable, lpMeas, lpMeas.aestronglyMeasurable
-/
theorem aestronglyMeasurable_condExpL2 (hm : m <= m0) (f : α ->₂[μ] E) :
    AEStronglyMeasurable[m] (condExpL2 E 𝕜 hm f : α -> E) μ :=
  lpMeas.aestronglyMeasurable _

/--
theorem `integrableOn_condExpL2_of_measure_ne_top` / 定理 `integrableOn_condExpL2_of_measure_ne_top`

English:
theorem integrableOn_condExpL2_of_measure_ne_top
  given: (hm : m <= m0) (hμs : μ s != ∞) (f : α ->₂[μ] E)
  proof: integrableOn_Lp_of_measure_ne_top (condExpL2 E 𝕜 hm f : α ->₂[μ] E) fact_one_le_two_ennreal.elim
    hμs

中文:
定理 integrableOn_condExpL2_of_measure_ne_top
  条件: (hm : m <= m0) (hμs : μ s != ∞) (f : α ->₂[μ] E)
  证明: integrableOn_Lp_of_measure_ne_top (condExpL2 E 𝕜 hm f : α ->₂[μ] E) fact_one_le_two_ennreal.elim
    hμs

Depends on / 依赖: condExpL2
-/
theorem integrableOn_condExpL2_of_measure_ne_top (hm : m <= m0) (hμs : μ s != ∞) (f : α ->₂[μ] E) :
    IntegrableOn (ε := E) (condExpL2 E 𝕜 hm f) s μ :=
  integrableOn_Lp_of_measure_ne_top (condExpL2 E 𝕜 hm f : α ->₂[μ] E) fact_one_le_two_ennreal.elim
    hμs

/--
theorem `integrable_condExpL2_of_isFiniteMeasure` / 定理 `integrable_condExpL2_of_isFiniteMeasure`

English:
theorem integrable_condExpL2_of_isFiniteMeasure
  given: (hm : m <= m0) [IsFiniteMeasure μ] {f : α ->₂[μ] E}
  proof: integrableOn_univ.mp integrableOn_condExpL2_of_measure_ne_top hm (measure_ne_top _ _) f

中文:
定理 integrable_condExpL2_of_isFiniteMeasure
  条件: (hm : m <= m0) [是有限测度 μ] {f : α ->₂[μ] E}
  证明: integrableOn_univ.mp integrableOn_condExpL2_of_measure_ne_top hm (measure_ne_top _ _) f

Depends on / 依赖: condExpL2
-/
theorem integrable_condExpL2_of_isFiniteMeasure (hm : m <= m0) [IsFiniteMeasure μ] {f : α ->₂[μ] E} :
    Integrable (ε := E) (condExpL2 E 𝕜 hm f) μ :=
integrableOn_univ.mp integrableOn_condExpL2_of_measure_ne_top hm (measure_ne_top _ _) f

/--
theorem `norm_condExpL2_le_one` / 定理 `norm_condExpL2_le_one`

English:
theorem norm_condExpL2_le_one
  given: (hm : m <= m0)
  statement: ‖@condExpL2 α E 𝕜 _ _ _ _ _ _ μ hm‖ <= 1
  proof: haveI : Fact (m <= m0) := ⟨hm⟩
  Submodule.orthogonalProjectionOnto_norm_le _

中文:
定理 norm_condExpL2_le_one
  条件: (hm : m <= m0)
  结论: ‖@condExpL2 α E 𝕜 _ _ _ _ _ _ μ hm‖ <= 1
  证明: haveI : Fact (m <= m0) := ⟨hm⟩
  Submodule.orthogonalProjectionOnto_norm_le _

Depends on / 依赖: Submodule, Submodule.orthogonalProjectionOnto_norm_le, orthogonalProjectionOnto_norm_le
-/
theorem norm_condExpL2_le_one (hm : m <= m0) : ‖@condExpL2 α E 𝕜 _ _ _ _ _ _ μ hm‖ <= 1 :=
  haveI : Fact (m <= m0) := ⟨hm⟩
  Submodule.orthogonalProjectionOnto_norm_le _

/--
theorem `norm_condExpL2_le` / 定理 `norm_condExpL2_le`

English:
theorem norm_condExpL2_le
  given: (hm : m <= m0) (f : α ->₂[μ] E)
  statement: ‖condExpL2 E 𝕜 hm f‖ <= ‖f‖
  proof: ((@condExpL2 _ E 𝕜 _ _ _ _ _ _ μ hm).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condExpL2_le_one hm))

中文:
定理 norm_condExpL2_le
  条件: (hm : m <= m0) (f : α ->₂[μ] E)
  结论: ‖condExpL2 E 𝕜 hm f‖ <= ‖f‖
  证明: ((@condExpL2 _ E 𝕜 _ _ _ _ _ _ μ hm).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condExpL2_le_one hm))

Depends on / 依赖: condExpL2, le_opNorm, mul_le_of_le_one_left, norm_condExpL2_le_one, norm_nonneg
-/
theorem norm_condExpL2_le (hm : m <= m0) (f : α ->₂[μ] E) : ‖condExpL2 E 𝕜 hm f‖ <= ‖f‖ :=
  ((@condExpL2 _ E 𝕜 _ _ _ _ _ _ μ hm).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condExpL2_le_one hm))

/--
theorem `eLpNorm_condExpL2_le` / 定理 `eLpNorm_condExpL2_le`

English:
theorem eLpNorm_condExpL2_le
  given: (hm : m <= m0) (f : α ->₂[μ] E)
  proof: by
  rw [← ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)]; rw [←
    Lp.norm_def]; rw [← Lp.norm_def]; rw [Submodule.norm_coe]
  exact norm_condExpL2_le hm f

中文:
定理 eLpNorm_condExpL2_le
  条件: (hm : m <= m0) (f : α ->₂[μ] E)
  证明: by
  rw [← ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)]; rw [←
    Lp.norm_def]; rw [← Lp.norm_def]; rw [Submodule.norm_coe]
  exact norm_condExpL2_le hm f

Depends on / 依赖: ENNReal, ENNReal.toReal_le_toReal, Lp.eLpNorm_ne_top, Lp.norm_def, Submodule, Submodule.norm_coe, condExpL2, eLpNorm, eLpNorm_ne_top, norm_coe, norm_condExpL2_le, norm_def, toReal_le_toReal
-/
theorem eLpNorm_condExpL2_le (hm : m <= m0) (f : α ->₂[μ] E) :
    eLpNorm (ε := E) (condExpL2 E 𝕜 hm f) 2 μ <= eLpNorm f 2 μ := by
  rw [← ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)]; rw [←
    Lp.norm_def]; rw [← Lp.norm_def]; rw [Submodule.norm_coe]
  exact norm_condExpL2_le hm f

/--
theorem `norm_condExpL2_coe_le` / 定理 `norm_condExpL2_coe_le`

English:
theorem norm_condExpL2_coe_le
  given: (hm : m <= m0) (f : α ->₂[μ] E)
  proof: by
  rw [Lp.norm_def]; rw [Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_condExpL2_le hm f)

中文:
定理 norm_condExpL2_coe_le
  条件: (hm : m <= m0) (f : α ->₂[μ] E)
  证明: by
  rw [Lp.norm_def]; rw [Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_condExpL2_le hm f)

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, Lp.eLpNorm_ne_top, Lp.norm_def, eLpNorm_condExpL2_le, eLpNorm_ne_top, norm_def, toReal_mono
-/
theorem norm_condExpL2_coe_le (hm : m <= m0) (f : α ->₂[μ] E) :
    ‖(condExpL2 E 𝕜 hm f : α ->₂[μ] E)‖ <= ‖f‖ := by
  rw [Lp.norm_def]; rw [Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_condExpL2_le hm f)

/--
theorem `inner_condExpL2_left_eq_right` / 定理 `inner_condExpL2_left_eq_right`

English:
theorem inner_condExpL2_left_eq_right
  given: (hm : m <= m0) {f g : α ->₂[μ] E}
  proof: haveI : Fact (m <= m0) := ⟨hm⟩
  Submodule.inner_starProjection_left_eq_right _ f g

中文:
定理 inner_condExpL2_left_eq_right
  条件: (hm : m <= m0) {f g : α ->₂[μ] E}
  证明: haveI : Fact (m <= m0) := ⟨hm⟩
  Submodule.inner_starProjection_left_eq_right _ f g

Depends on / 依赖: Submodule, Submodule.inner_starProjection_left_eq_right, inner_starProjection_left_eq_right
-/
theorem inner_condExpL2_left_eq_right (hm : m <= m0) {f g : α ->₂[μ] E} :
    ⟪(condExpL2 E 𝕜 hm f : α ->₂[μ] E), g⟫ = ⟪f, (condExpL2 E 𝕜 hm g : α ->₂[μ] E)⟫ :=
  haveI : Fact (m <= m0) := ⟨hm⟩
  Submodule.inner_starProjection_left_eq_right _ f g

/--
theorem `condExpL2_indicator_of_measurable` / 定理 `condExpL2_indicator_of_measurable`

English:
theorem condExpL2_indicator_of_measurable
  statement: (hm : m <= m0) (hs : MeasurableSet[m] s) (hμs : μ s != ∞)
  proof: by
  rw [condExpL2]
  have : Fact (m <= m0) := ⟨hm⟩
  have h_mem : indicatorConstLp 2 (hm s hs) hμs c in lpMeas E 𝕜 m 2 μ :=
    mem_lpMeas_indicatorConstLp hm hs hμs
  let ind := (⟨indicatorConstLp 2 (hm s hs) hμs c, h_mem⟩ : lpMeas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α ->₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c := rfl
  have h_orth_mem := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ind
  rw [← h_coe_ind]; rw [h_orth_mem]

中文:
定理 condExpL2_indicator_of_measurable
  结论: (hm : m <= m0) (hs : 可测集[m] s) (hμs : μ s != ∞)
  证明: by
  rw [condExpL2]
  have : Fact (m <= m0) := ⟨hm⟩
  have h_mem : indicatorConstLp 2 (hm s hs) hμs c in lpMeas E 𝕜 m 2 μ :=
    mem_lpMeas_indicatorConstLp hm hs hμs
  let ind := (⟨indicatorConstLp 2 (hm s hs) hμs c, h_mem⟩ : lpMeas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α ->₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c := rfl
  have h_orth_mem := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ind
  rw [← h_coe_ind]; rw [h_orth_mem]

Depends on / 依赖: Submodule, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, condExpL2, h_coe_ind, h_mem, h_orth_mem, indicatorConstLp, lpMeas, mem_lpMeas_indicatorConstLp, orthogonalProjectionOnto_mem_subspace_eq_self
-/
theorem condExpL2_indicator_of_measurable (hm : m <= m0) (hs : MeasurableSet[m] s) (hμs : μ s != ∞)
    (c : E) :
    (condExpL2 E 𝕜 hm (indicatorConstLp 2 (hm s hs) hμs c) : α ->₂[μ] E) =
      indicatorConstLp 2 (hm s hs) hμs c := by
  rw [condExpL2]
  have : Fact (m <= m0) := ⟨hm⟩
  have h_mem : indicatorConstLp 2 (hm s hs) hμs c in lpMeas E 𝕜 m 2 μ :=
    mem_lpMeas_indicatorConstLp hm hs hμs
  let ind := (⟨indicatorConstLp 2 (hm s hs) hμs c, h_mem⟩ : lpMeas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α ->₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c := rfl
  have h_orth_mem := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ind
  rw [← h_coe_ind]; rw [h_orth_mem]

/--
theorem `inner_condExpL2_eq_inner_fun` / 定理 `inner_condExpL2_eq_inner_fun`

English:
theorem inner_condExpL2_eq_inner_fun
  statement: (hm : m <= m0) (f g : α ->₂[μ] E)
  proof: by
  symm
  rw [← sub_eq_zero]; rw [← inner_sub_left]; rw [condExpL2]
  simp only [← Submodule.starProjection_apply,
    mem_lpMeas_iff_aestronglyMeasurable.mpr hg,
    Submodule.starProjection_inner_eq_zero f g]

中文:
定理 inner_condExpL2_eq_inner_fun
  结论: (hm : m <= m0) (f g : α ->₂[μ] E)
  证明: by
  symm
  rw [← sub_eq_zero]; rw [← inner_sub_left]; rw [condExpL2]
  simp only [← Submodule.starProjection_apply,
    mem_lpMeas_iff_aestronglyMeasurable.mpr hg,
    Submodule.starProjection_inner_eq_zero f g]

Depends on / 依赖: Submodule, Submodule.starProjection_apply, Submodule.starProjection_inner_eq_zero, condExpL2, inner_sub_left, mem_lpMeas_iff_aestronglyMeasurable, mem_lpMeas_iff_aestronglyMeasurable.mpr, starProjection_apply, starProjection_inner_eq_zero, sub_eq_zero
-/
theorem inner_condExpL2_eq_inner_fun (hm : m <= m0) (f g : α ->₂[μ] E)
    (hg : AEStronglyMeasurable[m] g μ) :
    ⟪(condExpL2 E 𝕜 hm f : α ->₂[μ] E), g⟫ = ⟪f, g⟫ := by
  symm
  rw [← sub_eq_zero]; rw [← inner_sub_left]; rw [condExpL2]
  simp only [← Submodule.starProjection_apply,
    mem_lpMeas_iff_aestronglyMeasurable.mpr hg,
    Submodule.starProjection_inner_eq_zero f g]

section Real

variable {hm : m <= m0}

/--
theorem `integral_condExpL2_eq_of_fin_meas_real` / 定理 `integral_condExpL2_eq_of_fin_meas_real`

English:
theorem integral_condExpL2_eq_of_fin_meas_real
  statement: (f : Lp 𝕜 2 μ) (hs : MeasurableSet[m] s)
  proof: by
  rw [← L2.inner_indicatorConstLp_one (𝕜 := 𝕜) (hm s hs) hμs f]
  have h_eq_inner : ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α -> 𝕜) x ∂μ =
      ⟪indicatorConstLp 2 (hm s hs) hμs (1 : 𝕜), condExpL2 𝕜 𝕜 hm f⟫ := by
    rw [L2.inner_indicatorConstLp_one (hm s hs) hμs]
  rw [h_eq_inner]; rw [← inner_condExpL2_left_eq_right]; rw [condExpL2_indicator_of_measurable hm hs hμs]

中文:
定理 integral_condExpL2_eq_of_fin_meas_real
  结论: (f : Lp 𝕜 2 μ) (hs : 可测集[m] s)
  证明: by
  rw [← L2.inner_indicatorConstLp_one (𝕜 := 𝕜) (hm s hs) hμs f]
  have h_eq_inner : ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α -> 𝕜) x ∂μ =
      ⟪indicatorConstLp 2 (hm s hs) hμs (1 : 𝕜), condExpL2 𝕜 𝕜 hm f⟫ := by
    rw [L2.inner_indicatorConstLp_one (hm s hs) hμs]
  rw [h_eq_inner]; rw [← inner_condExpL2_left_eq_right]; rw [condExpL2_indicator_of_measurable hm hs hμs]

Depends on / 依赖: L2.inner_indicatorConstLp_one, condExpL2, condExpL2_indicator_of_measurable, h_eq_inner, indicatorConstLp, inner_condExpL2_left_eq_right, inner_indicatorConstLp_one
-/
theorem integral_condExpL2_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s != ∞) : ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α -> 𝕜) x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← L2.inner_indicatorConstLp_one (𝕜 := 𝕜) (hm s hs) hμs f]
  have h_eq_inner : ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α -> 𝕜) x ∂μ =
      ⟪indicatorConstLp 2 (hm s hs) hμs (1 : 𝕜), condExpL2 𝕜 𝕜 hm f⟫ := by
    rw [L2.inner_indicatorConstLp_one (hm s hs) hμs]
  rw [h_eq_inner]; rw [← inner_condExpL2_left_eq_right]; rw [condExpL2_indicator_of_measurable hm hs hμs]

/--
theorem `lintegral_nnnorm_condExpL2_le` / 定理 `lintegral_nnnorm_condExpL2_le`

English:
theorem lintegral_nnnorm_condExpL2_le
  given: (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (f : Lp Real 2 μ)
  proof: by
  let h_meas := lpMeas.aestronglyMeasurable (condExpL2 Real Real hm f)
  let g := h_meas.choose
  have hg_meas : StronglyMeasurable[m] g := h_meas.choose_spec.1
  have hg_eq : g =ᵐ[μ] condExpL2 Real Real hm f := h_meas.choose_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condExpL2 Real Real hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq : (fun x => (‖g x‖₊ : Real>=0∞)) =ᵐ[μ.restrict s] fun x =>
      (‖(condExpL2 Real Real hm f : α -> Real) x‖₊ : Real>=0∞) := by
    refine hg_eq_restrict.mono fun x hx => ?_
    dsimp only
    simp_rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine lintegral_enorm_le_of_forall_fin_meas_integral_eq
    hm (Lp.stronglyMeasurable f) ?_ ?_ ?_ ?_ hs hμs
  · exact integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
  · exact hg_meas
  · rw [IntegrableOn, integrable_congr hg_eq_restrict]
    exact integrableOn_condExpL2_of_measure_ne_top hm hμs f
  · intro t ht hμt
    rw [← integral_condExpL2_eq_of_fin_meas_real (hm := hm) f ht hμt.ne]
    exact setIntegral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)

中文:
定理 lintegral_nnnorm_condExpL2_le
  条件: (hs : 可测集[m] s) (hμs : μ s != ∞) (f : Lp 实数 2 μ)
  证明: by
  let h_meas := lpMeas.aestronglyMeasurable (condExpL2 Real Real hm f)
  let g := h_meas.choose
  have hg_meas : StronglyMeasurable[m] g := h_meas.choose_spec.1
  have hg_eq : g =ᵐ[μ] condExpL2 Real Real hm f := h_meas.choose_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condExpL2 Real Real hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq : (fun x => (‖g x‖₊ : Real>=0∞)) =ᵐ[μ.restrict s] fun x =>
      (‖(condExpL2 Real Real hm f : α -> Real) x‖₊ : Real>=0∞) := by
    refine hg_eq_restrict.mono fun x hx => ?_
    dsimp only
    simp_rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine lintegral_enorm_le_of_forall_fin_meas_integral_eq
    hm (Lp.stronglyMeasurable f) ?_ ?_ ?_ ?_ hs hμs
  · exact integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
  · exact hg_meas
  · rw [IntegrableOn, integrable_congr hg_eq_restrict]
    exact integrableOn_condExpL2_of_measure_ne_top hm hμs f
  · intro t ht hμt
    rw [← integral_condExpL2_eq_of_fin_meas_real (hm := hm) f ht hμt.ne]
    exact setIntegral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)

Depends on / 依赖: StronglyMeasurable, ae_restrict_of_ae, aestronglyMeasurable, choose_spec, condExpL2, h_meas, h_meas.choose, h_meas.choose_spec, hg_eq, hg_eq_restrict, hg_eq_restrict.mono, hg_meas, hg_nnnorm_eq, lpMeas, lpMeas.aestronglyMeasurable, restrict
-/
theorem lintegral_nnnorm_condExpL2_le (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (f : Lp Real 2 μ) :
    ∫⁻ x in s, ‖(condExpL2 Real Real hm f : α -> Real) x‖₊ ∂μ <= ∫⁻ x in s, ‖f x‖₊ ∂μ := by
  let h_meas := lpMeas.aestronglyMeasurable (condExpL2 Real Real hm f)
  let g := h_meas.choose
  have hg_meas : StronglyMeasurable[m] g := h_meas.choose_spec.1
  have hg_eq : g =ᵐ[μ] condExpL2 Real Real hm f := h_meas.choose_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condExpL2 Real Real hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq : (fun x => (‖g x‖₊ : Real>=0∞)) =ᵐ[μ.restrict s] fun x =>
      (‖(condExpL2 Real Real hm f : α -> Real) x‖₊ : Real>=0∞) := by
    refine hg_eq_restrict.mono fun x hx => ?_
    dsimp only
    simp_rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine lintegral_enorm_le_of_forall_fin_meas_integral_eq
    hm (Lp.stronglyMeasurable f) ?_ ?_ ?_ ?_ hs hμs
  · exact integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
  · exact hg_meas
  · rw [IntegrableOn, integrable_congr hg_eq_restrict]
    exact integrableOn_condExpL2_of_measure_ne_top hm hμs f
  · intro t ht hμt
    rw [← integral_condExpL2_eq_of_fin_meas_real (hm := hm) f ht hμt.ne]
    exact setIntegral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)

/--
theorem `condExpL2_ae_eq_zero_of_ae_eq_zero` / 定理 `condExpL2_ae_eq_zero_of_ae_eq_zero`

English:
theorem condExpL2_ae_eq_zero_of_ae_eq_zero
  statement: (hs : MeasurableSet[m] s) (hμs : μ s != ∞) {f : Lp Real 2 μ}
  proof: by
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, ‖(condExpL2 Real Real hm f : α -> Real) x‖₊ ∂μ = 0 by
    rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero
    · refine h_nnnorm_eq_zero.mono fun x hx => ?_
      dsimp only at hx
      rw [Pi.zero_apply] at hx ⊢
      · rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero] at hx
    · refine Measurable.coe_nnreal_ennreal (Measurable.nnnorm ?_)
      exact (Lp.stronglyMeasurable _).measurable
  rw [← nonpos_iff_eq_zero]
  refine (lintegral_nnnorm_condExpL2_le hs hμs f).trans (le_of_eq ?_)
  rw [lintegral_eq_zero_iff]
  · refine hf.mono fun x hx => ?_
    dsimp only
    rw [hx]
    simp
  · exact (Lp.stronglyMeasurable _).enorm (ε := Real)

中文:
定理 condExpL2_ae_eq_zero_of_ae_eq_zero
  结论: (hs : 可测集[m] s) (hμs : μ s != ∞) {f : Lp 实数 2 μ}
  证明: by
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, ‖(condExpL2 Real Real hm f : α -> Real) x‖₊ ∂μ = 0 by
    rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero
    · refine h_nnnorm_eq_zero.mono fun x hx => ?_
      dsimp only at hx
      rw [Pi.zero_apply] at hx ⊢
      · rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero] at hx
    · refine Measurable.coe_nnreal_ennreal (Measurable.nnnorm ?_)
      exact (Lp.stronglyMeasurable _).measurable
  rw [← nonpos_iff_eq_zero]
  refine (lintegral_nnnorm_condExpL2_le hs hμs f).trans (le_of_eq ?_)
  rw [lintegral_eq_zero_iff]
  · refine hf.mono fun x hx => ?_
    dsimp only
    rw [hx]
    simp
  · exact (Lp.stronglyMeasurable _).enorm (ε := Real)

Depends on / 依赖: ENNReal, ENNReal.coe_eq_zero, Lp.stronglyMeasurable, Measurable, Measurable.coe_nnreal_ennreal, Measurable.nnnorm, Pi.zero_apply, coe_eq_zero, coe_nnreal_ennreal, condExpL2, h_nnnorm_eq_zero, h_nnnorm_eq_zero.mono, le_of_eq, lintegral_eq_z, lintegral_eq_zero_iff, lintegral_nnnorm_condExpL2_le, measurable, nnnorm, nnnorm_eq_zero, nonpos_iff_eq_zero
-/
theorem condExpL2_ae_eq_zero_of_ae_eq_zero (hs : MeasurableSet[m] s) (hμs : μ s != ∞) {f : Lp Real 2 μ}
    (hf : f =ᵐ[μ.restrict s] 0) : condExpL2 Real Real hm f =ᵐ[μ.restrict s] (0 : α -> Real) := by
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, ‖(condExpL2 Real Real hm f : α -> Real) x‖₊ ∂μ = 0 by
    rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero
    · refine h_nnnorm_eq_zero.mono fun x hx => ?_
      dsimp only at hx
      rw [Pi.zero_apply] at hx ⊢
      · rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero] at hx
    · refine Measurable.coe_nnreal_ennreal (Measurable.nnnorm ?_)
      exact (Lp.stronglyMeasurable _).measurable
  rw [← nonpos_iff_eq_zero]
  refine (lintegral_nnnorm_condExpL2_le hs hμs f).trans (le_of_eq ?_)
  rw [lintegral_eq_zero_iff]
  · refine hf.mono fun x hx => ?_
    dsimp only
    rw [hx]
    simp
  · exact (Lp.stronglyMeasurable _).enorm (ε := Real)

/--
theorem `lintegral_nnnorm_condExpL2_indicator_le_real` / 定理 `lintegral_nnnorm_condExpL2_indicator_le_real`

English:
theorem lintegral_nnnorm_condExpL2_indicator_le_real
  statement: (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: by
  refine (lintegral_nnnorm_condExpL2_le ht hμt _).trans (le_of_eq ?_)
  have h_eq :
    ∫⁻ x in t, ‖(indicatorConstLp 2 hs hμs (1 : Real)) x‖₊ ∂μ =
      ∫⁻ x in t, s.indicator (fun _ => (1 : Real>=0∞)) x ∂μ := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    refine (@indicatorConstLp_coeFn _ _ _ 2 _ _ _ hs hμs (1 : Real)).mono fun x hx => ?_
    dsimp only
    rw [hx]
    classical
    simp_rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [h_eq]; rw [lintegral_indicator hs]; rw [lintegral_const]; rw [Measure.restrict_restrict hs]
  simp only [one_mul, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]

中文:
定理 lintegral_nnnorm_condExpL2_indicator_le_real
  结论: (hs : 可测集 s) (hμs : μ s != ∞)
  证明: by
  refine (lintegral_nnnorm_condExpL2_le ht hμt _).trans (le_of_eq ?_)
  have h_eq :
    ∫⁻ x in t, ‖(indicatorConstLp 2 hs hμs (1 : Real)) x‖₊ ∂μ =
      ∫⁻ x in t, s.indicator (fun _ => (1 : Real>=0∞)) x ∂μ := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    refine (@indicatorConstLp_coeFn _ _ _ 2 _ _ _ hs hμs (1 : Real)).mono fun x hx => ?_
    dsimp only
    rw [hx]
    classical
    simp_rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [h_eq]; rw [lintegral_indicator hs]; rw [lintegral_const]; rw [Measure.restrict_restrict hs]
  simp only [one_mul, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]

Depends on / 依赖: Measure, Measure.restrict_re, Set.indicator_apply, ae_restrict_of_ae, classical, h_eq, indicator, indicatorConstLp, indicatorConstLp_coeFn, indicator_apply, le_of_eq, lintegral_congr_ae, lintegral_const, lintegral_indicator, lintegral_nnnorm_condExpL2_le, restrict_re, s.indicator, simp_rw, split_ifs
-/
theorem lintegral_nnnorm_condExpL2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s != ∞)
    (ht : MeasurableSet[m] t) (hμt : μ t != ∞) :
    ∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a‖₊ ∂μ <= μ (s inter t) := by
  refine (lintegral_nnnorm_condExpL2_le ht hμt _).trans (le_of_eq ?_)
  have h_eq :
    ∫⁻ x in t, ‖(indicatorConstLp 2 hs hμs (1 : Real)) x‖₊ ∂μ =
      ∫⁻ x in t, s.indicator (fun _ => (1 : Real>=0∞)) x ∂μ := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    refine (@indicatorConstLp_coeFn _ _ _ 2 _ _ _ hs hμs (1 : Real)).mono fun x hx => ?_
    dsimp only
    rw [hx]
    classical
    simp_rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [h_eq]; rw [lintegral_indicator hs]; rw [lintegral_const]; rw [Measure.restrict_restrict hs]
  simp only [one_mul, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]

end Real

/--
theorem `condExpL2_const_inner` / 定理 `condExpL2_const_inner`

English:
theorem condExpL2_const_inner
  given: (hm : m <= m0) (f : Lp E 2 μ) (c : E)
  proof: by
  have h_mem_Lp : MemLp (fun a => ⟪c, (condExpL2 E 𝕜 hm f : α -> E) a⟫) 2 μ := by
    refine MemLp.const_inner _ ?_; exact Lp.memLp _
  have h_eq : h_mem_Lp.toLp _ =ᵐ[μ] fun a => ⟪c, (condExpL2 E 𝕜 hm f : α -> E) a⟫ :=
    h_mem_Lp.coeFn_toLp
  refine EventuallyEq.trans ?_ h_eq
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜 hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) ?_ ?_ ?_ ?_
  · intro s _ hμs
    rw [IntegrableOn]; rw [integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _).const_inner _
  · intro s hs hμs
    rw [integral_condExpL2_eq_of_fin_meas_real _ hs hμs.ne]; rw [integral_congr_ae (ae_restrict_of_ae h_eq)]; rw [←
      L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 (↑(condExpL2 E 𝕜 hm f)) (hm s hs) c hμs.ne]; rw [← inner_condExpL2_left_eq_right]; rw [condExpL2_indicator_of_measurable _ hs]; rw [L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 f (hm s hs) c hμs.ne]; rw [setIntegral_congr_ae (hm s hs)
        ((MemLp.coeFn_toLp ((Lp.memLp f).const_inner c)).mono fun x hx _ => hx)]
  · exact lpMeas.aestronglyMeasurable _
  · refine AEStronglyMeasurable.congr ?_ h_eq.symm
    exact (lpMeas.aestronglyMeasurable _).const_inner

中文:
定理 condExpL2_const_inner
  条件: (hm : m <= m0) (f : Lp E 2 μ) (c : E)
  证明: by
  have h_mem_Lp : MemLp (fun a => ⟪c, (condExpL2 E 𝕜 hm f : α -> E) a⟫) 2 μ := by
    refine MemLp.const_inner _ ?_; exact Lp.memLp _
  have h_eq : h_mem_Lp.toLp _ =ᵐ[μ] fun a => ⟪c, (condExpL2 E 𝕜 hm f : α -> E) a⟫ :=
    h_mem_Lp.coeFn_toLp
  refine EventuallyEq.trans ?_ h_eq
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜 hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) ?_ ?_ ?_ ?_
  · intro s _ hμs
    rw [IntegrableOn]; rw [integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _).const_inner _
  · intro s hs hμs
    rw [integral_condExpL2_eq_of_fin_meas_real _ hs hμs.ne]; rw [integral_congr_ae (ae_restrict_of_ae h_eq)]; rw [←
      L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 (↑(condExpL2 E 𝕜 hm f)) (hm s hs) c hμs.ne]; rw [← inner_condExpL2_left_eq_right]; rw [condExpL2_indicator_of_measurable _ hs]; rw [L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 f (hm s hs) c hμs.ne]; rw [setIntegral_congr_ae (hm s hs)
        ((MemLp.coeFn_toLp ((Lp.memLp f).const_inner c)).mono fun x hx _ => hx)]
  · exact lpMeas.aestronglyMeasurable _
  · refine AEStronglyMeasurable.congr ?_ h_eq.symm
    exact (lpMeas.aestronglyMeasurable _).const_inner

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, EventuallyEq, EventuallyEq.trans, IntegrableOn, Lp.ae_eq_of_forall_setIntegral_eq, Lp.memLp, MemLp.const_inner, ae_eq_of_forall_setIntegral_eq, ae_restrict, coeFn_toLp, coe_ne_top, condExpL2, const_inner, h_eq, h_mem_Lp, h_mem_Lp.coeFn_toLp, h_mem_Lp.toLp, integrableOn_condExpL2_of_measure_ne_top, integrable_congr
-/
theorem condExpL2_const_inner (hm : m <= m0) (f : Lp E 2 μ) (c : E) :
    condExpL2 𝕜 𝕜 hm (((Lp.memLp f).const_inner c).toLp fun a => ⟪c, f a⟫) =ᵐ[μ]
    fun a => ⟪c, (condExpL2 E 𝕜 hm f : α -> E) a⟫ := by
  have h_mem_Lp : MemLp (fun a => ⟪c, (condExpL2 E 𝕜 hm f : α -> E) a⟫) 2 μ := by
    refine MemLp.const_inner _ ?_; exact Lp.memLp _
  have h_eq : h_mem_Lp.toLp _ =ᵐ[μ] fun a => ⟪c, (condExpL2 E 𝕜 hm f : α -> E) a⟫ :=
    h_mem_Lp.coeFn_toLp
  refine EventuallyEq.trans ?_ h_eq
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜 hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) ?_ ?_ ?_ ?_
  · intro s _ hμs
    rw [IntegrableOn]; rw [integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _).const_inner _
  · intro s hs hμs
    rw [integral_condExpL2_eq_of_fin_meas_real _ hs hμs.ne]; rw [integral_congr_ae (ae_restrict_of_ae h_eq)]; rw [←
      L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 (↑(condExpL2 E 𝕜 hm f)) (hm s hs) c hμs.ne]; rw [← inner_condExpL2_left_eq_right]; rw [condExpL2_indicator_of_measurable _ hs]; rw [L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 f (hm s hs) c hμs.ne]; rw [setIntegral_congr_ae (hm s hs)
        ((MemLp.coeFn_toLp ((Lp.memLp f).const_inner c)).mono fun x hx _ => hx)]
  · exact lpMeas.aestronglyMeasurable _
  · refine AEStronglyMeasurable.congr ?_ h_eq.symm
    exact (lpMeas.aestronglyMeasurable _).const_inner

/--
theorem `integral_condExpL2_eq` / 定理 `integral_condExpL2_eq`

English:
theorem integral_condExpL2_eq
  statement: (hm : m <= m0) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s)
  proof: by
  rw [← sub_eq_zero]; rw [←
    integral_sub' (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)]
  refine integral_eq_zero_of_forall_integral_inner_eq_zero 𝕜 _ ?_ ?_
  · rw [integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub (↑(condExpL2 E' 𝕜 hm f)) f).symm)]
    exact integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw [integral_sub
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)]
  have h_ae_eq_f := MemLp.coeFn_toLp (E := 𝕜) ((Lp.memLp f).const_inner c)
  rw [sub_eq_zero]; rw [←
    setIntegral_congr_ae (hm s hs) ((condExpL2_const_inner hm f c).mono fun x hx _ => hx)]; rw [←
    setIntegral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condExpL2_eq_of_fin_meas_real _ hs hμs

中文:
定理 integral_condExpL2_eq
  结论: (hm : m <= m0) (f : Lp E' 2 μ) (hs : 可测集[m] s)
  证明: by
  rw [← sub_eq_zero]; rw [←
    integral_sub' (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)]
  refine integral_eq_zero_of_forall_integral_inner_eq_zero 𝕜 _ ?_ ?_
  · rw [integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub (↑(condExpL2 E' 𝕜 hm f)) f).symm)]
    exact integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw [integral_sub
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)]
  have h_ae_eq_f := MemLp.coeFn_toLp (E := 𝕜) ((Lp.memLp f).const_inner c)
  rw [sub_eq_zero]; rw [←
    setIntegral_congr_ae (hm s hs) ((condExpL2_const_inner hm f c).mono fun x hx _ => hx)]; rw [←
    setIntegral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condExpL2_eq_of_fin_meas_real _ hs hμs

Depends on / 依赖: Lp.coeFn_sub, Pi.sub_apply, ae_restrict_of_ae, coeFn_sub, condExpL2, fact_one_le_two_ennreal, fact_one_le_two_ennreal.elim, inner_sub_right, integrableOn_L, integrableOn_Lp_of_measure_ne_top, integrable_congr, integral_eq_zero_of_forall_integral_inner_eq_zero, integral_sub, simp_rw, sub_apply, sub_eq_zero
-/
theorem integral_condExpL2_eq (hm : m <= m0) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s != ∞) : ∫ x in s, (condExpL2 E' 𝕜 hm f : α -> E') x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← sub_eq_zero]; rw [←
    integral_sub' (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)]
  refine integral_eq_zero_of_forall_integral_inner_eq_zero 𝕜 _ ?_ ?_
  · rw [integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub (↑(condExpL2 E' 𝕜 hm f)) f).symm)]
    exact integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw [integral_sub
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)]
  have h_ae_eq_f := MemLp.coeFn_toLp (E := 𝕜) ((Lp.memLp f).const_inner c)
  rw [sub_eq_zero]; rw [←
    setIntegral_congr_ae (hm s hs) ((condExpL2_const_inner hm f c).mono fun x hx _ => hx)]; rw [←
    setIntegral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condExpL2_eq_of_fin_meas_real _ hs hμs

variable {E'' 𝕜' : Type*} [RCLike 𝕜'] [NormedAddCommGroup E''] [InnerProductSpace 𝕜' E'']
  [CompleteSpace E''] [NormedSpace Real E'']

variable (𝕜 𝕜')

/--
theorem `condExpL2_comp_continuousLinearMap` / 定理 `condExpL2_comp_continuousLinearMap`

English:
theorem condExpL2_comp_continuousLinearMap
  given: (hm : m <= m0) (T : E' ->L[Real] E'') (f : α ->₂[μ] E')
  proof: by
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜' hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) (fun s _ hμs =>
      integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne) ?_ ?_ ?_
  · intro s hs hμs
    rw [T.setIntegral_compLp _ (hm s hs)]; rw [T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne)]; rw [integral_condExpL2_eq hm f hs hμs.ne]; rw [integral_condExpL2_eq hm (T.compLp f) hs hμs.ne]; rw [T.setIntegral_compLp _ (hm s hs)]; rw [T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)]
  · exact lpMeas.aestronglyMeasurable _
  · have h_coe := T.coeFn_compLp (condExpL2 E' 𝕜 hm f : α ->₂[μ] E')
    rw [← EventuallyEq] at h_coe
    refine AEStronglyMeasurable.congr ?_ h_coe.symm
    exact T.continuous.comp_aestronglyMeasurable (lpMeas.aestronglyMeasurable (condExpL2 E' 𝕜 hm f))

中文:
定理 condExpL2_comp_continuousLinearMap
  条件: (hm : m <= m0) (T : E' ->L[实数] E'') (f : α ->₂[μ] E')
  证明: by
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜' hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) (fun s _ hμs =>
      integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne) ?_ ?_ ?_
  · intro s hs hμs
    rw [T.setIntegral_compLp _ (hm s hs)]; rw [T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne)]; rw [integral_condExpL2_eq hm f hs hμs.ne]; rw [integral_condExpL2_eq hm (T.compLp f) hs hμs.ne]; rw [T.setIntegral_compLp _ (hm s hs)]; rw [T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)]
  · exact lpMeas.aestronglyMeasurable _
  · have h_coe := T.coeFn_compLp (condExpL2 E' 𝕜 hm f : α ->₂[μ] E')
    rw [← EventuallyEq] at h_coe
    refine AEStronglyMeasurable.congr ?_ h_coe.symm
    exact T.continuous.comp_aestronglyMeasurable (lpMeas.aestronglyMeasurable (condExpL2 E' 𝕜 hm f))

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, Lp.ae_eq_of_forall_setIntegral_eq, T.compLp, T.integral_comp_comm, T.setIntegral_compLp, ae_eq_of_forall_setIntegral_eq, coe_ne_top, compLp, fact_one_le_two_ennreal, fact_one_le_two_ennreal.elim, integrableOn_Lp_of_measure_ne_top, integrableOn_condExpL2_of_measure_ne_top, integral_comp_comm, integral_condExpL2_eq, s.ne, setIntegral_compLp, two_ne_zero
-/
theorem condExpL2_comp_continuousLinearMap (hm : m <= m0) (T : E' ->L[Real] E'') (f : α ->₂[μ] E') :
    (condExpL2 E'' 𝕜' hm (T.compLp f) : α ->₂[μ] E'') =ᵐ[μ]
    T.compLp (condExpL2 E' 𝕜 hm f : α ->₂[μ] E') := by
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜' hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) (fun s _ hμs =>
      integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne) ?_ ?_ ?_
  · intro s hs hμs
    rw [T.setIntegral_compLp _ (hm s hs)]; rw [T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne)]; rw [integral_condExpL2_eq hm f hs hμs.ne]; rw [integral_condExpL2_eq hm (T.compLp f) hs hμs.ne]; rw [T.setIntegral_compLp _ (hm s hs)]; rw [T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)]
  · exact lpMeas.aestronglyMeasurable _
  · have h_coe := T.coeFn_compLp (condExpL2 E' 𝕜 hm f : α ->₂[μ] E')
    rw [← EventuallyEq] at h_coe
    refine AEStronglyMeasurable.congr ?_ h_coe.symm
    exact T.continuous.comp_aestronglyMeasurable (lpMeas.aestronglyMeasurable (condExpL2 E' 𝕜 hm f))

variable {𝕜 𝕜'}

section CondexpL2Indicator

variable (𝕜)

/--
theorem `condExpL2_indicator_ae_eq_smul` / 定理 `condExpL2_indicator_ae_eq_smul`

English:
theorem condExpL2_indicator_ae_eq_smul
  statement: (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: by
  rw [indicatorConstLp_eq_toSpanSingleton_compLp hs hμs x]
  have h_comp :=
    condExpL2_comp_continuousLinearMap Real 𝕜 hm (toSpanSingleton Real x)
      (indicatorConstLp 2 hs hμs (1 : Real))
  refine h_comp.trans ?_
  exact (toSpanSingleton Real x).coeFn_compLp _

中文:
定理 condExpL2_indicator_ae_eq_smul
  结论: (hm : m <= m0) (hs : 可测集 s) (hμs : μ s != ∞)
  证明: by
  rw [indicatorConstLp_eq_toSpanSingleton_compLp hs hμs x]
  have h_comp :=
    condExpL2_comp_continuousLinearMap Real 𝕜 hm (toSpanSingleton Real x)
      (indicatorConstLp 2 hs hμs (1 : Real))
  refine h_comp.trans ?_
  exact (toSpanSingleton Real x).coeFn_compLp _

Depends on / 依赖: coeFn_compLp, condExpL2_comp_continuousLinearMap, h_comp, h_comp.trans, indicatorConstLp, indicatorConstLp_eq_toSpanSingleton_compLp, toSpanSingleton
-/
theorem condExpL2_indicator_ae_eq_smul (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
    (x : E') :
    condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) =ᵐ[μ] fun a =>
      (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs (1 : Real)) : α -> Real) a • x := by
  rw [indicatorConstLp_eq_toSpanSingleton_compLp hs hμs x]
  have h_comp :=
    condExpL2_comp_continuousLinearMap Real 𝕜 hm (toSpanSingleton Real x)
      (indicatorConstLp 2 hs hμs (1 : Real))
  refine h_comp.trans ?_
  exact (toSpanSingleton Real x).coeFn_compLp _

/--
theorem `condExpL2_indicator_eq_toSpanSingleton_comp` / 定理 `condExpL2_indicator_eq_toSpanSingleton_comp`

English:
theorem condExpL2_indicator_eq_toSpanSingleton_comp
  statement: (hm : m <= m0) (hs : MeasurableSet s)
  proof: by
  ext1
  refine (condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans ?_
  have h_comp := (toSpanSingleton Real x).coeFn_compLp
    (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α ->₂[μ] Real)
  rw [← EventuallyEq] at h_comp
  refine EventuallyEq.trans ?_ h_comp.symm
  filter_upwards with y using rfl

中文:
定理 condExpL2_indicator_eq_toSpanSingleton_comp
  结论: (hm : m <= m0) (hs : 可测集 s)
  证明: by
  ext1
  refine (condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans ?_
  have h_comp := (toSpanSingleton Real x).coeFn_compLp
    (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α ->₂[μ] Real)
  rw [← EventuallyEq] at h_comp
  refine EventuallyEq.trans ?_ h_comp.symm
  filter_upwards with y using rfl

Depends on / 依赖: EventuallyEq, EventuallyEq.trans, coeFn_compLp, condExpL2, condExpL2_indicator_ae_eq_smul, filter_upwards, h_comp, h_comp.symm, indicatorConstLp, toSpanSingleton
-/
theorem condExpL2_indicator_eq_toSpanSingleton_comp (hm : m <= m0) (hs : MeasurableSet s)
    (hμs : μ s != ∞) (x : E') : (condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α ->₂[μ] E') =
    (toSpanSingleton Real x).compLp (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1)) := by
  ext1
  refine (condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans ?_
  have h_comp := (toSpanSingleton Real x).coeFn_compLp
    (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α ->₂[μ] Real)
  rw [← EventuallyEq] at h_comp
  refine EventuallyEq.trans ?_ h_comp.symm
  filter_upwards with y using rfl

variable {𝕜}

/--
theorem `setLIntegral_nnnorm_condExpL2_indicator_le` / 定理 `setLIntegral_nnnorm_condExpL2_indicator_le`

English:
theorem setLIntegral_nnnorm_condExpL2_indicator_le
  statement: (hm : m <= m0) (hs : MeasurableSet s)
  proof: calc
    ∫⁻ a in t, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α -> E') a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := Real)
    _ <= μ (s inter t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]

中文:
定理 setL整数egral_nnnorm_condExpL2_indicator_le
  结论: (hm : m <= m0) (hs : 可测集 s)
  证明: calc
    ∫⁻ a in t, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α -> E') a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := Real)
    _ <= μ (s inter t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]

Depends on / 依赖: ENNReal, ENNReal.coe_mul, Lp.stronglyMeasurable, coe_mul, condExpL2, condExpL2_indicator_ae_eq_smul, indicatorConstLp, lintegral_mul_const, nnnorm_smul, setLIntegral_congr_fun_ae, simp_rw, stronglyMeasurable
-/
theorem setLIntegral_nnnorm_condExpL2_indicator_le (hm : m <= m0) (hs : MeasurableSet s)
    (hμs : μ s != ∞) (x : E') {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ t != ∞) :
    ∫⁻ a in t, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α -> E') a‖₊ ∂μ <=
    μ (s inter t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α -> E') a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := Real)
    _ <= μ (s inter t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]

/--
theorem `lintegral_nnnorm_condExpL2_indicator_le` / 定理 `lintegral_nnnorm_condExpL2_indicator_le`

English:
theorem lintegral_nnnorm_condExpL2_indicator_le
  statement: (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

中文:
定理 lintegral_nnnorm_condExpL2_indicator_le
  结论: (hm : m <= m0) (hs : 可测集 s) (hμs : μ s != ∞)
  证明: by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

Depends on / 依赖: Set.inter_subset_left, inter_subset_left, lintegral_le_of_forall_fin_meas_trim_le, setLIntegral_nnnorm_condExpL2_indicator_le
-/
theorem lintegral_nnnorm_condExpL2_indicator_le (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
    (x : E') [SigmaFinite (μ.trim hm)] :
    ∫⁻ a, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α -> E') a‖₊ ∂μ <= μ s * ‖x‖₊ := by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

/--
theorem `integrable_condExpL2_indicator` / 定理 `integrable_condExpL2_indicator`

English:
theorem integrable_condExpL2_indicator
  statement: (hm : m <= m0) [SigmaFinite (μ.trim hm)]
  proof: by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt =>
      (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left

中文:
定理 integrable_condExpL2_indicator
  结论: (hm : m <= m0) [σ有限 (μ.trim hm)]
  证明: by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt =>
      (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, Lp.aestronglyMeasurable, Set.inter_subset_left, aestronglyMeasurable, coe_lt_top, condExpL2, indicatorConstLp, integrable_of_forall_fin_meas_le, inter_subset_left, lt_top, mul_lt_top, s.lt_top, setLIntegral_nnnorm_condExpL2_indicator_le
-/
theorem integrable_condExpL2_indicator (hm : m <= m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E') :
    Integrable (ε := E') (condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x)) μ := by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt =>
      (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left

end CondexpL2Indicator

section CondexpIndSMul

variable [NormedSpace Real G] {hm : m <= m0}

/--
Definition of `condExpIndSMul` / `condExpIndSMul` 的定义

English:
definition condExpIndSMul
  signature: (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G)
  body: (toSpanSingleton Real x).compLpL 2 μ (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs (1 : Real)))

中文:
定义 condExpIndSMul
  签名: (hm : m <= m0) (hs : 可测集 s) (hμs : μ s != ∞) (x : G)
  定义体: (toSpanSingleton Real x).compLpL 2 μ (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs (1 : Real)))

Depends on / 依赖: compLpL, condExpL2, indicatorConstLp, toSpanSingleton
-/
noncomputable def condExpIndSMul (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) :
    Lp G 2 μ :=
  (toSpanSingleton Real x).compLpL 2 μ (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs (1 : Real)))

/--
theorem `aestronglyMeasurable_condExpIndSMul` / 定理 `aestronglyMeasurable_condExpIndSMul`

English:
theorem aestronglyMeasurable_condExpIndSMul
  statement: (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: by
  have h : AEStronglyMeasurable[m] (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) μ :=
    aestronglyMeasurable_condExpL2 _ _
  rw [condExpIndSMul]
  exact ((toSpanSingleton Real x).continuous.comp_aestronglyMeasurable h).congr
    (coeFn_compLpL _ _).symm

中文:
定理 aestronglyMeasurable_condExpIndSMul
  结论: (hm : m <= m0) (hs : 可测集 s) (hμs : μ s != ∞)
  证明: by
  have h : AEStronglyMeasurable[m] (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) μ :=
    aestronglyMeasurable_condExpL2 _ _
  rw [condExpIndSMul]
  exact ((toSpanSingleton Real x).continuous.comp_aestronglyMeasurable h).congr
    (coeFn_compLpL _ _).symm

Depends on / 依赖: AEStronglyMeasurable, aestronglyMeasurable_condExpL2, coeFn_compLpL, comp_aestronglyMeasurable, condExpIndSMul, condExpL2, continuous, continuous.comp_aestronglyMeasurable, indicatorConstLp, toSpanSingleton
-/
theorem aestronglyMeasurable_condExpIndSMul (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
    (x : G) : AEStronglyMeasurable[m] (condExpIndSMul hm hs hμs x) μ := by
  have h : AEStronglyMeasurable[m] (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) μ :=
    aestronglyMeasurable_condExpL2 _ _
  rw [condExpIndSMul]
  exact ((toSpanSingleton Real x).continuous.comp_aestronglyMeasurable h).congr
    (coeFn_compLpL _ _).symm

/--
theorem `condExpIndSMul_add` / 定理 `condExpIndSMul_add`

English:
theorem condExpIndSMul_add
  given: (hs : MeasurableSet s) (hμs : μ s != ∞) (x y : G)
  proof: by
  simp_rw [condExpIndSMul]; rw [toSpanSingleton_add, add_compLpL, add_apply]

中文:
定理 condExpIndSMul_add
  条件: (hs : 可测集 s) (hμs : μ s != ∞) (x y : G)
  证明: by
  simp_rw [condExpIndSMul]; rw [toSpanSingleton_add, add_compLpL, add_apply]

Depends on / 依赖: add_apply, add_compLpL, condExpIndSMul, simp_rw, toSpanSingleton_add
-/
theorem condExpIndSMul_add (hs : MeasurableSet s) (hμs : μ s != ∞) (x y : G) :
    condExpIndSMul hm hs hμs (x + y) = condExpIndSMul hm hs hμs x + condExpIndSMul hm hs hμs y := by
  simp_rw [condExpIndSMul]; rw [toSpanSingleton_add, add_compLpL, add_apply]

/--
theorem `condExpIndSMul_smul` / 定理 `condExpIndSMul_smul`

English:
theorem condExpIndSMul_smul
  statement: [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (hs : MeasurableSet s)
  proof: by
  simp_rw [condExpIndSMul, toSpanSingleton_smul, smul_compLpL, smul_apply]

中文:
定理 condExpIndSMul_smul
  结论: [赋范空间 实数 F] [标量交换类 实数 𝕜 F] (hs : 可测集 s)
  证明: by
  simp_rw [condExpIndSMul, toSpanSingleton_smul, smul_compLpL, smul_apply]

Depends on / 依赖: condExpIndSMul, simp_rw, smul_apply, smul_compLpL, toSpanSingleton_smul
-/
theorem condExpIndSMul_smul [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s != ∞) (c : 𝕜) (x : F) :
    condExpIndSMul hm hs hμs (c • x) = c • condExpIndSMul hm hs hμs x := by
  simp_rw [condExpIndSMul, toSpanSingleton_smul, smul_compLpL, smul_apply]

/--
theorem `condExpIndSMul_ae_eq_smul` / 定理 `condExpIndSMul_ae_eq_smul`

English:
theorem condExpIndSMul_ae_eq_smul
  given: (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G)
  proof: (toSpanSingleton Real x).coeFn_compLpL _

中文:
定理 condExpIndSMul_ae_eq_smul
  条件: (hm : m <= m0) (hs : 可测集 s) (hμs : μ s != ∞) (x : G)
  证明: (toSpanSingleton Real x).coeFn_compLpL _

Depends on / 依赖: coeFn_compLpL, toSpanSingleton
-/
theorem condExpIndSMul_ae_eq_smul (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) :
    condExpIndSMul hm hs hμs x =ᵐ[μ] fun a =>
      (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a • x :=
  (toSpanSingleton Real x).coeFn_compLpL _

/--
theorem `setLIntegral_nnnorm_condExpIndSMul_le` / 定理 `setLIntegral_nnnorm_condExpIndSMul_le`

English:
theorem setLIntegral_nnnorm_condExpIndSMul_le
  statement: (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: calc
    ∫⁻ a in t, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpIndSMul_ae_eq_smul hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := Real)
    _ <= μ (s inter t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]

中文:
定理 setL整数egral_nnnorm_condExpIndSMul_le
  结论: (hm : m <= m0) (hs : 可测集 s) (hμs : μ s != ∞)
  证明: calc
    ∫⁻ a in t, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpIndSMul_ae_eq_smul hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := Real)
    _ <= μ (s inter t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]

Depends on / 依赖: ENNReal, ENNReal.coe_mul, Lp.stronglyMeasurable, coe_mul, condExpIndSMul, condExpIndSMul_ae_eq_smul, condExpL2, indicatorConstLp, lintegral_mul_const, nnnorm_smul, setLIntegral_congr_fun_ae, simp_rw, stronglyMeasurable
-/
theorem setLIntegral_nnnorm_condExpIndSMul_le (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
    (x : G) {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ t != ∞) :
    (∫⁻ a in t, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ) <= μ (s inter t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpIndSMul_ae_eq_smul hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := Real)
    _ <= μ (s inter t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]

/--
theorem `lintegral_nnnorm_condExpIndSMul_le` / 定理 `lintegral_nnnorm_condExpIndSMul_le`

English:
theorem lintegral_nnnorm_condExpIndSMul_le
  statement: (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

中文:
定理 lintegral_nnnorm_condExpIndSMul_le
  结论: (hm : m <= m0) (hs : 可测集 s) (hμs : μ s != ∞)
  证明: by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

Depends on / 依赖: Set.inter_subset_left, inter_subset_left, lintegral_le_of_forall_fin_meas_trim_le, setLIntegral_nnnorm_condExpIndSMul_le
-/
theorem lintegral_nnnorm_condExpIndSMul_le (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
    (x : G) [SigmaFinite (μ.trim hm)] : ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ <= μ s * ‖x‖₊ := by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

/--
theorem `integrable_condExpIndSMul` / 定理 `integrable_condExpIndSMul`

English:
theorem integrable_condExpIndSMul
  statement: (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
  proof: by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt => (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left

中文:
定理 integrable_condExpIndSMul
  结论: (hm : m <= m0) [σ有限 (μ.trim hm)] (hs : 可测集 s)
  证明: by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt => (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, Lp.aestronglyMeasurable, Set.inter_subset_left, aestronglyMeasurable, coe_lt_top, integrable_of_forall_fin_meas_le, inter_subset_left, lt_top, mul_lt_top, s.lt_top, setLIntegral_nnnorm_condExpIndSMul_le
-/
theorem integrable_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s != ∞) (x : G) : Integrable (condExpIndSMul hm hs hμs x) μ := by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt => (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left

/--
theorem `condExpIndSMul_empty` / 定理 `condExpIndSMul_empty`

English:
theorem condExpIndSMul_empty
  given: {x : G}
  statement: condExpIndSMul hm MeasurableSet.empty
  proof: by
  rw [condExpIndSMul]; rw [indicatorConstLp_empty]
  simp only [Submodule.coe_zero, map_zero]

中文:
定理 condExpIndSMul_empty
  条件: {x : G}
  结论: condExpIndSMul hm 可测集.empty
  证明: by
  rw [condExpIndSMul]; rw [indicatorConstLp_empty]
  simp only [Submodule.coe_zero, map_zero]

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, Submodule, Submodule.coe_zero, coe_lt_top, coe_zero, condExpIndSMul, indicatorConstLp_empty, le.trans_lt, map_zero, trans_lt
-/
theorem condExpIndSMul_empty {x : G} : condExpIndSMul hm MeasurableSet.empty
    ((measure_empty (μ := μ)).le.trans_lt ENNReal.coe_lt_top).ne x = 0 := by
  rw [condExpIndSMul]; rw [indicatorConstLp_empty]
  simp only [Submodule.coe_zero, map_zero]

/--
theorem `setIntegral_condExpL2_indicator` / 定理 `setIntegral_condExpL2_indicator`

English:
theorem setIntegral_condExpL2_indicator
  statement: (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
  proof: calc
    ∫ x in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) x ∂μ =
        ∫ x in s, indicatorConstLp 2 ht hμt (1 : Real) x ∂μ :=
      @integral_condExpL2_eq α _ Real _ _ _ _ _ _ _ _ _ hm (indicatorConstLp 2 ht hμt (1 : Real)) hs hμs
    _ = μ.real (t inter s) • (1 : Real) := setIntegral_indicatorConstLp (hm s hs) ht hμt 1
    _ = μ.real (t inter s) := by rw [smul_eq_mul, mul_one]

中文:
定理 set整数egral_condExpL2_indicator
  结论: (hs : 可测集[m] s) (ht : 可测集 t)
  证明: calc
    ∫ x in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) x ∂μ =
        ∫ x in s, indicatorConstLp 2 ht hμt (1 : Real) x ∂μ :=
      @integral_condExpL2_eq α _ Real _ _ _ _ _ _ _ _ _ hm (indicatorConstLp 2 ht hμt (1 : Real)) hs hμs
    _ = μ.real (t inter s) • (1 : Real) := setIntegral_indicatorConstLp (hm s hs) ht hμt 1
    _ = μ.real (t inter s) := by rw [smul_eq_mul, mul_one]

Depends on / 依赖: condExpL2, indicatorConstLp, integral_condExpL2_eq, mul_one, setIntegral_indicatorConstLp, smul_eq_mul
-/
theorem setIntegral_condExpL2_indicator (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
    (hμs : μ s != ∞) (hμt : μ t != ∞) :
    ∫ x in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) x ∂μ = μ.real (t inter s) :=
  calc
    ∫ x in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) x ∂μ =
        ∫ x in s, indicatorConstLp 2 ht hμt (1 : Real) x ∂μ :=
      @integral_condExpL2_eq α _ Real _ _ _ _ _ _ _ _ _ hm (indicatorConstLp 2 ht hμt (1 : Real)) hs hμs
    _ = μ.real (t inter s) • (1 : Real) := setIntegral_indicatorConstLp (hm s hs) ht hμt 1
    _ = μ.real (t inter s) := by rw [smul_eq_mul, mul_one]

/--
theorem `setIntegral_condExpIndSMul` / 定理 `setIntegral_condExpIndSMul`

English:
theorem setIntegral_condExpIndSMul
  statement: (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
  proof: calc
    ∫ a in s, (condExpIndSMul hm ht hμt x) a ∂μ =
        ∫ a in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) a • x ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpIndSMul_ae_eq_smul hm ht hμt x).mono fun _ hx _ => hx)
    _ = (∫ a in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) a ∂μ) • x :=
      (integral_smul_const _ x)
    _ = μ.real (t inter s) • x := by rw [setIntegral_condExpL2_indicator hs ht hμs hμt]

中文:
定理 set整数egral_condExpIndSMul
  结论: (hs : 可测集[m] s) (ht : 可测集 t)
  证明: calc
    ∫ a in s, (condExpIndSMul hm ht hμt x) a ∂μ =
        ∫ a in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) a • x ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpIndSMul_ae_eq_smul hm ht hμt x).mono fun _ hx _ => hx)
    _ = (∫ a in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) a ∂μ) • x :=
      (integral_smul_const _ x)
    _ = μ.real (t inter s) • x := by rw [setIntegral_condExpL2_indicator hs ht hμs hμt]

Depends on / 依赖: condExpIndSMul, condExpIndSMul_ae_eq_smul, condExpL2, indicatorConstLp, integral_smul_const, setIntegral_condExpL2_indicator, setIntegral_congr_ae
-/
theorem setIntegral_condExpIndSMul (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
    (hμs : μ s != ∞) (hμt : μ t != ∞) (x : G') :
    ∫ a in s, (condExpIndSMul hm ht hμt x) a ∂μ = μ.real (t inter s) • x :=
  calc
    ∫ a in s, (condExpIndSMul hm ht hμt x) a ∂μ =
        ∫ a in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) a • x ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpIndSMul_ae_eq_smul hm ht hμt x).mono fun _ hx _ => hx)
    _ = (∫ a in s, (condExpL2 Real Real hm (indicatorConstLp 2 ht hμt 1) : α -> Real) a ∂μ) • x :=
      (integral_smul_const _ x)
    _ = μ.real (t inter s) • x := by rw [setIntegral_condExpL2_indicator hs ht hμs hμt]

/--
theorem `condExpL2_indicator_nonneg` / 定理 `condExpL2_indicator_nonneg`

English:
theorem condExpL2_indicator_nonneg
  statement: (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: by
  have h : AEStronglyMeasurable[m] (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) μ :=
    aestronglyMeasurable_condExpL2 _ _
  refine EventuallyLE.trans_eq ?_ h.ae_eq_mk.symm
  refine @ae_le_of_ae_le_trim _ _ _ _ _ _ hm (0 : α -> Real) _ ?_
  refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
  · rintro t - -
    refine @Integrable.integrableOn _ _ m _ _ _ _ _ ?_
    refine Integrable.trim hm ?_ h.stronglyMeasurable_mk
    rw [integrable_congr h.ae_eq_mk.symm]
    exact integrable_condExpL2_indicator hm hs hμs _
  · intro t ht hμt
    rw [← setIntegral_trim hm h.stronglyMeasurable_mk ht]
    have h_ae :
        forallᵐ x ∂μ, x in t -> h.mk _ x = (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) x := by
      filter_upwards [h.ae_eq_mk] with x hx using fun _ => hx.symm
    rw [setIntegral_congr_ae (hm t ht) h_ae]; rw [setIntegral_condExpL2_indicator ht hs ((le_trim hm).trans_lt hμt).ne hμs]
    exact ENNReal.toReal_nonneg

中文:
定理 condExpL2_indicator_nonneg
  结论: (hm : m <= m0) (hs : 可测集 s) (hμs : μ s != ∞)
  证明: by
  have h : AEStronglyMeasurable[m] (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) μ :=
    aestronglyMeasurable_condExpL2 _ _
  refine EventuallyLE.trans_eq ?_ h.ae_eq_mk.symm
  refine @ae_le_of_ae_le_trim _ _ _ _ _ _ hm (0 : α -> Real) _ ?_
  refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
  · rintro t - -
    refine @Integrable.integrableOn _ _ m _ _ _ _ _ ?_
    refine Integrable.trim hm ?_ h.stronglyMeasurable_mk
    rw [integrable_congr h.ae_eq_mk.symm]
    exact integrable_condExpL2_indicator hm hs hμs _
  · intro t ht hμt
    rw [← setIntegral_trim hm h.stronglyMeasurable_mk ht]
    have h_ae :
        forallᵐ x ∂μ, x in t -> h.mk _ x = (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) x := by
      filter_upwards [h.ae_eq_mk] with x hx using fun _ => hx.symm
    rw [setIntegral_congr_ae (hm t ht) h_ae]; rw [setIntegral_condExpL2_indicator ht hs ((le_trim hm).trans_lt hμt).ne hμs]
    exact ENNReal.toReal_nonneg

Depends on / 依赖: AEStronglyMeasurable, EventuallyLE, EventuallyLE.trans_eq, Integrable, Integrable.integrableOn, Integrable.trim, ae_eq_mk, ae_le_of_ae_le_trim, ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite, aestronglyMeasurable_condExpL2, condExpL2, h.ae_eq_mk.symm, h.stronglyMeasurable_mk, indicatorConstLp, integrableOn, integrable_cond, integrable_congr, stronglyMeasurable_mk, trans_eq
-/
theorem condExpL2_indicator_nonneg (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞)
    [SigmaFinite (μ.trim hm)] : (0 : α -> Real) <=ᵐ[μ]
    condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) := by
  have h : AEStronglyMeasurable[m] (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) μ :=
    aestronglyMeasurable_condExpL2 _ _
  refine EventuallyLE.trans_eq ?_ h.ae_eq_mk.symm
  refine @ae_le_of_ae_le_trim _ _ _ _ _ _ hm (0 : α -> Real) _ ?_
  refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
  · rintro t - -
    refine @Integrable.integrableOn _ _ m _ _ _ _ _ ?_
    refine Integrable.trim hm ?_ h.stronglyMeasurable_mk
    rw [integrable_congr h.ae_eq_mk.symm]
    exact integrable_condExpL2_indicator hm hs hμs _
  · intro t ht hμt
    rw [← setIntegral_trim hm h.stronglyMeasurable_mk ht]
    have h_ae :
        forallᵐ x ∂μ, x in t -> h.mk _ x = (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) x := by
      filter_upwards [h.ae_eq_mk] with x hx using fun _ => hx.symm
    rw [setIntegral_congr_ae (hm t ht) h_ae]; rw [setIntegral_condExpL2_indicator ht hs ((le_trim hm).trans_lt hμt).ne hμs]
    exact ENNReal.toReal_nonneg

/--
theorem `condExpIndSMul_nonneg` / 定理 `condExpIndSMul_nonneg`

English:
theorem condExpIndSMul_nonneg
  statement: {E}
  proof: by
  refine EventuallyLE.trans_eq ?_ (condExpIndSMul_ae_eq_smul hm hs hμs x).symm
  filter_upwards [condExpL2_indicator_nonneg hm hs hμs] with a ha
  exact smul_nonneg ha hx

中文:
定理 condExpIndSMul_nonneg
  结论: {E}
  证明: by
  refine EventuallyLE.trans_eq ?_ (condExpIndSMul_ae_eq_smul hm hs hμs x).symm
  filter_upwards [condExpL2_indicator_nonneg hm hs hμs] with a ha
  exact smul_nonneg ha hx

Depends on / 依赖: EventuallyLE, EventuallyLE.trans_eq, condExpIndSMul_ae_eq_smul, condExpL2_indicator_nonneg, filter_upwards, smul_nonneg, trans_eq
-/
theorem condExpIndSMul_nonneg {E}
    [NormedAddCommGroup E] [PartialOrder E] [NormedSpace Real E] [IsOrderedModule Real E]
    [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E) (hx : 0 <= x) :
    (0 : α -> E) <=ᵐ[μ] condExpIndSMul hm hs hμs x := by
  refine EventuallyLE.trans_eq ?_ (condExpIndSMul_ae_eq_smul hm hs hμs x).symm
  filter_upwards [condExpL2_indicator_nonneg hm hs hμs] with a ha
  exact smul_nonneg ha hx

end CondexpIndSMul

end MeasureTheory
