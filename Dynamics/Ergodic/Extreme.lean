/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.Dynamics.Ergodic.RadonNikodym
public import Mathlib.Probability.ConditionalProbability

/-!
# Ergodic measures as extreme points

In this file we prove that a finite measure `μ` is an ergodic measure for a self-map `f`
iff it is an extreme point of the set of invariant measures of `f` with the same total volume.
We also specialize this result to probability measures.
-/

public section

open Filter Set Function MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {X : Type*} {m : MeasurableSpace X} {μ ν : Measure X} {f : X -> X}

namespace Ergodic

/--
theorem `of_mem_extremePoints_measure_univ_eq` / 定理 `of_mem_extremePoints_measure_univ_eq`

English:
theorem of_mem_extremePoints_measure_univ_eq
  statement: {c : Real>=0∞} (hc : c != ∞)
  proof: by
  have hf : MeasurePreserving f μ μ := h.1.1
  rcases eq_or_ne c 0 with rfl | hc₀
  · convert! zero_measure hf.measurable
    rw [← measure_univ_eq_zero]; rw [h.1.2]
  · refine ⟨hf, ⟨?_⟩⟩
    have : IsFiniteMeasure μ := by
      constructor
      rwa [h.1.2, lt_top_iff_ne_top]
    set S := {ν | MeasurePreserving f ν ν ∧ ν univ = c}
    have {s : Set X} (hsm : MeasurableSet s) (hfs : f ⁻¹' s = s) (hμs : μ s != 0) :
        c • μ[|s] in S := by
      refine ⟨.smul_measure (.smul_measure ?_ _) c, ?_⟩
      · convert! hf.restrict_preimage hsm
        exact hfs.symm
      · rw [Measure.smul_apply, (cond_isProbabilityMeasure hμs).1, smul_eq_mul, mul_one]
    intro s hsm hfs
    by_contra H
    obtain ⟨hs, hs'⟩ : μ s != 0 ∧ μ sᶜ != 0 := by
      simpa [eventuallyConst_set, ae_iff, and_comm] using! H
    have hcond : c • μ[|s] = μ := by
      apply h.2 (this hsm hfs hs) (this hsm.compl (by rw [preimage_compl, hfs]) hs')
      refine ⟨μ s / c, μ sᶜ / c, ENNReal.div_pos hs hc, ENNReal.div_pos hs' hc, ?_, ?_⟩
      · rw [← ENNReal.add_div, measure_add_measure_compl hsm, h.1.2, ENNReal.div_self hc₀ hc]
      · simp [ProbabilityTheory.cond, smul_smul, ← mul_assoc, ENNReal.div_mul_cancel,
          ENNReal.mul_inv_cancel, *]
    rw [← hcond] at hs'
    simp [ProbabilityTheory.cond_apply, hsm] at hs'

中文:
定理 of_mem_extremePoints_measure_univ_eq
  结论: {c : 实数>=0∞} (hc : c != ∞)
  证明: by
  have hf : MeasurePreserving f μ μ := h.1.1
  rcases eq_or_ne c 0 with rfl | hc₀
  · convert! zero_measure hf.measurable
    rw [← measure_univ_eq_zero]; rw [h.1.2]
  · refine ⟨hf, ⟨?_⟩⟩
    have : IsFiniteMeasure μ := by
      constructor
      rwa [h.1.2, lt_top_iff_ne_top]
    set S := {ν | MeasurePreserving f ν ν ∧ ν univ = c}
    have {s : Set X} (hsm : MeasurableSet s) (hfs : f ⁻¹' s = s) (hμs : μ s != 0) :
        c • μ[|s] in S := by
      refine ⟨.smul_measure (.smul_measure ?_ _) c, ?_⟩
      · convert! hf.restrict_preimage hsm
        exact hfs.symm
      · rw [Measure.smul_apply, (cond_isProbabilityMeasure hμs).1, smul_eq_mul, mul_one]
    intro s hsm hfs
    by_contra H
    obtain ⟨hs, hs'⟩ : μ s != 0 ∧ μ sᶜ != 0 := by
      simpa [eventuallyConst_set, ae_iff, and_comm] using! H
    have hcond : c • μ[|s] = μ := by
      apply h.2 (this hsm hfs hs) (this hsm.compl (by rw [preimage_compl, hfs]) hs')
      refine ⟨μ s / c, μ sᶜ / c, ENNReal.div_pos hs hc, ENNReal.div_pos hs' hc, ?_, ?_⟩
      · rw [← ENNReal.add_div, measure_add_measure_compl hsm, h.1.2, ENNReal.div_self hc₀ hc]
      · simp [ProbabilityTheory.cond, smul_smul, ← mul_assoc, ENNReal.div_mul_cancel,
          ENNReal.mul_inv_cancel, *]
    rw [← hcond] at hs'
    simp [ProbabilityTheory.cond_apply, hsm] at hs'

Depends on / 依赖: IsFiniteMeasure, MeasurableSet, MeasurePreserving, convert, eq_or_ne, hf.measurable, hf.restrict_preimage, lt_top_iff_ne_top, measurable, measure_univ_eq_zero, restrict_preimage, smul_measure, zero_measure
-/
theorem of_mem_extremePoints_measure_univ_eq {c : Real>=0∞} (hc : c != ∞)
    (h : μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = c}) : Ergodic f μ := by
  have hf : MeasurePreserving f μ μ := h.1.1
  rcases eq_or_ne c 0 with rfl | hc₀
  · convert! zero_measure hf.measurable
    rw [← measure_univ_eq_zero]; rw [h.1.2]
  · refine ⟨hf, ⟨?_⟩⟩
    have : IsFiniteMeasure μ := by
      constructor
      rwa [h.1.2, lt_top_iff_ne_top]
    set S := {ν | MeasurePreserving f ν ν ∧ ν univ = c}
    have {s : Set X} (hsm : MeasurableSet s) (hfs : f ⁻¹' s = s) (hμs : μ s != 0) :
        c • μ[|s] in S := by
      refine ⟨.smul_measure (.smul_measure ?_ _) c, ?_⟩
      · convert! hf.restrict_preimage hsm
        exact hfs.symm
      · rw [Measure.smul_apply, (cond_isProbabilityMeasure hμs).1, smul_eq_mul, mul_one]
    intro s hsm hfs
    by_contra H
    obtain ⟨hs, hs'⟩ : μ s != 0 ∧ μ sᶜ != 0 := by
      simpa [eventuallyConst_set, ae_iff, and_comm] using! H
    have hcond : c • μ[|s] = μ := by
      apply h.2 (this hsm hfs hs) (this hsm.compl (by rw [preimage_compl, hfs]) hs')
      refine ⟨μ s / c, μ sᶜ / c, ENNReal.div_pos hs hc, ENNReal.div_pos hs' hc, ?_, ?_⟩
      · rw [← ENNReal.add_div, measure_add_measure_compl hsm, h.1.2, ENNReal.div_self hc₀ hc]
      · simp [ProbabilityTheory.cond, smul_smul, ← mul_assoc, ENNReal.div_mul_cancel,
          ENNReal.mul_inv_cancel, *]
    rw [← hcond] at hs'
    simp [ProbabilityTheory.cond_apply, hsm] at hs'

/--
theorem `of_mem_extremePoints` / 定理 `of_mem_extremePoints`

English:
theorem of_mem_extremePoints
  proof: .of_mem_extremePoints_measure_univ_eq ENNReal.one_ne_top by
    simpa only [isProbabilityMeasure_iff] using h

中文:
定理 of_mem_extremePoints
  证明: .of_mem_extremePoints_measure_univ_eq ENNReal.one_ne_top by
    simpa only [isProbabilityMeasure_iff] using h

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, isProbabilityMeasure_iff, of_mem_extremePoints_measure_univ_eq, one_ne_top
-/
theorem of_mem_extremePoints
    (h : μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}) :
    Ergodic f μ :=
.of_mem_extremePoints_measure_univ_eq ENNReal.one_ne_top by
    simpa only [isProbabilityMeasure_iff] using h

-- TODO: do we need `IsFiniteMeasure ν` here?
/--
theorem `eq_smul_of_absolutelyContinuous` / 定理 `eq_smul_of_absolutelyContinuous`

English:
theorem eq_smul_of_absolutelyContinuous
  statement: [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Ergodic f μ)
  proof: by
  have := hfν.rnDeriv_comp_aeEq hμ.toMeasurePreserving
  obtain ⟨c, hc⟩ := hμ.ae_eq_const_of_ae_eq_comp₀ (measurable_rnDeriv _ _).nullMeasurable this
  use c
  ext s hs
  calc
ν s = ∫⁻ a in s, ν.rnDeriv μ a ∂μ := .symm setLIntegral_rnDeriv hνμ _
_ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae hc.filter_mono ae_mono restrict_le_self
    _ = (c • μ) s := by simp

中文:
定理 eq_smul_of_absolutelyContinuous
  结论: [是有限测度 μ] [是有限测度 ν] (hμ : 遍历 f μ)
  证明: by
  have := hfν.rnDeriv_comp_aeEq hμ.toMeasurePreserving
  obtain ⟨c, hc⟩ := hμ.ae_eq_const_of_ae_eq_comp₀ (measurable_rnDeriv _ _).nullMeasurable this
  use c
  ext s hs
  calc
ν s = ∫⁻ a in s, ν.rnDeriv μ a ∂μ := .symm setLIntegral_rnDeriv hνμ _
_ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae hc.filter_mono ae_mono restrict_le_self
    _ = (c • μ) s := by simp

Depends on / 依赖: ae_mono, filter_mono, hc.filter_mono, lintegral_congr_ae, measurable_rnDeriv, nullMeasurable, restrict_le_self, rnDeriv, rnDeriv_comp_aeEq, setLIntegral_rnDeriv, toMeasurePreserving
-/
theorem eq_smul_of_absolutelyContinuous [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Ergodic f μ)
    (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : exists c : Real>=0∞, ν = c • μ := by
  have := hfν.rnDeriv_comp_aeEq hμ.toMeasurePreserving
  obtain ⟨c, hc⟩ := hμ.ae_eq_const_of_ae_eq_comp₀ (measurable_rnDeriv _ _).nullMeasurable this
  use c
  ext s hs
  calc
ν s = ∫⁻ a in s, ν.rnDeriv μ a ∂μ := .symm setLIntegral_rnDeriv hνμ _
_ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae hc.filter_mono ae_mono restrict_le_self
    _ = (c • μ) s := by simp

/--
theorem `eq_of_absolutelyContinuous_measure_univ_eq` / 定理 `eq_of_absolutelyContinuous_measure_univ_eq`

English:
theorem eq_of_absolutelyContinuous_measure_univ_eq
  statement: [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  rcases hμ.eq_smul_of_absolutelyContinuous hfν hνμ with ⟨c, rfl⟩
  rcases eq_or_ne μ 0 with rfl | hμ₀
  · simp
  · simp_all [ENNReal.mul_eq_right]

中文:
定理 eq_of_absolutelyContinuous_measure_univ_eq
  结论: [是有限测度 μ] [是有限测度 ν]
  证明: by
  rcases hμ.eq_smul_of_absolutelyContinuous hfν hνμ with ⟨c, rfl⟩
  rcases eq_or_ne μ 0 with rfl | hμ₀
  · simp
  · simp_all [ENNReal.mul_eq_right]

Depends on / 依赖: ENNReal, ENNReal.mul_eq_right, eq_or_ne, eq_smul_of_absolutelyContinuous, mul_eq_right
-/
theorem eq_of_absolutelyContinuous_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) (huniv : ν univ = μ univ) :
    ν = μ := by
  rcases hμ.eq_smul_of_absolutelyContinuous hfν hνμ with ⟨c, rfl⟩
  rcases eq_or_ne μ 0 with rfl | hμ₀
  · simp
  · simp_all [ENNReal.mul_eq_right]

/--
theorem `eq_of_absolutelyContinuous` / 定理 `eq_of_absolutelyContinuous`

English:
theorem eq_of_absolutelyContinuous
  statement: [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  proof: eq_of_absolutelyContinuous_measure_univ_eq hμ hfν hνμ by simp

中文:
定理 eq_of_absolutelyContinuous
  结论: [是概率测度 μ] [是概率测度 ν]
  证明: eq_of_absolutelyContinuous_measure_univ_eq hμ hfν hνμ by simp

Depends on / 依赖: eq_of_absolutelyContinuous_measure_univ_eq
-/
theorem eq_of_absolutelyContinuous [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ν = μ :=
eq_of_absolutelyContinuous_measure_univ_eq hμ hfν hνμ by simp

/--
theorem `mem_extremePoints_measure_univ_eq` / 定理 `mem_extremePoints_measure_univ_eq`

English:
theorem mem_extremePoints_measure_univ_eq
  given: [IsFiniteMeasure μ] (hμ : Ergodic f μ)
  proof: by
  rw [mem_extremePoints_iff_left]
  refine ⟨⟨hμ.toMeasurePreserving, rfl⟩, ?_⟩
  rintro ν₁ ⟨hfν₁, hν₁μ⟩ ν₂ ⟨hfν₂, hν₂μ⟩ ⟨a, b, ha, hb, hab, rfl⟩
  have : IsFiniteMeasure ν₁ := ⟨by rw [hν₁μ]; apply measure_lt_top⟩
  apply hμ.eq_of_absolutelyContinuous_measure_univ_eq hfν₁ (.add_right _ _) hν₁μ
  apply absolutelyContinuous_smul ha.ne'

中文:
定理 mem_extremePoints_measure_univ_eq
  条件: [是有限测度 μ] (hμ : 遍历 f μ)
  证明: by
  rw [mem_extremePoints_iff_left]
  refine ⟨⟨hμ.toMeasurePreserving, rfl⟩, ?_⟩
  rintro ν₁ ⟨hfν₁, hν₁μ⟩ ν₂ ⟨hfν₂, hν₂μ⟩ ⟨a, b, ha, hb, hab, rfl⟩
  have : IsFiniteMeasure ν₁ := ⟨by rw [hν₁μ]; apply measure_lt_top⟩
  apply hμ.eq_of_absolutelyContinuous_measure_univ_eq hfν₁ (.add_right _ _) hν₁μ
  apply absolutelyContinuous_smul ha.ne'

Depends on / 依赖: IsFiniteMeasure, absolutelyContinuous_smul, add_right, eq_of_absolutelyContinuous_measure_univ_eq, ha.ne, measure_lt_top, mem_extremePoints_iff_left, toMeasurePreserving
-/
theorem mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] (hμ : Ergodic f μ) :
    μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ} := by
  rw [mem_extremePoints_iff_left]
  refine ⟨⟨hμ.toMeasurePreserving, rfl⟩, ?_⟩
  rintro ν₁ ⟨hfν₁, hν₁μ⟩ ν₂ ⟨hfν₂, hν₂μ⟩ ⟨a, b, ha, hb, hab, rfl⟩
  have : IsFiniteMeasure ν₁ := ⟨by rw [hν₁μ]; apply measure_lt_top⟩
  apply hμ.eq_of_absolutelyContinuous_measure_univ_eq hfν₁ (.add_right _ _) hν₁μ
  apply absolutelyContinuous_smul ha.ne'

/--
theorem `mem_extremePoints` / 定理 `mem_extremePoints`

English:
theorem mem_extremePoints
  given: [IsProbabilityMeasure μ] (hμ : Ergodic f μ)
  proof: by
  simpa only [isProbabilityMeasure_iff, measure_univ] using hμ.mem_extremePoints_measure_univ_eq

中文:
定理 mem_extremePoints
  条件: [是概率测度 μ] (hμ : 遍历 f μ)
  证明: by
  simpa only [isProbabilityMeasure_iff, measure_univ] using hμ.mem_extremePoints_measure_univ_eq

Depends on / 依赖: isProbabilityMeasure_iff, measure_univ, mem_extremePoints_measure_univ_eq
-/
theorem mem_extremePoints [IsProbabilityMeasure μ] (hμ : Ergodic f μ) :
    μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} := by
  simpa only [isProbabilityMeasure_iff, measure_univ] using hμ.mem_extremePoints_measure_univ_eq

/--
theorem `iff_mem_extremePoints_measure_univ_eq` / 定理 `iff_mem_extremePoints_measure_univ_eq`

English:
theorem iff_mem_extremePoints_measure_univ_eq
  given: [IsFiniteMeasure μ]
  proof: ⟨mem_extremePoints_measure_univ_eq, of_mem_extremePoints_measure_univ_eq (measure_ne_top _ _)⟩

中文:
定理 iff_mem_extremePoints_measure_univ_eq
  条件: [是有限测度 μ]
  证明: ⟨mem_extremePoints_measure_univ_eq, of_mem_extremePoints_measure_univ_eq (measure_ne_top _ _)⟩

Depends on / 依赖: measure_ne_top, mem_extremePoints_measure_univ_eq, of_mem_extremePoints_measure_univ_eq
-/
theorem iff_mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] :
    Ergodic f μ ↔ μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ} :=
  ⟨mem_extremePoints_measure_univ_eq, of_mem_extremePoints_measure_univ_eq (measure_ne_top _ _)⟩

/--
theorem `iff_mem_extremePoints` / 定理 `iff_mem_extremePoints`

English:
theorem iff_mem_extremePoints
  given: [IsProbabilityMeasure μ]
  proof: ⟨mem_extremePoints, of_mem_extremePoints⟩

中文:
定理 iff_mem_extremePoints
  条件: [是概率测度 μ]
  证明: ⟨mem_extremePoints, of_mem_extremePoints⟩

Depends on / 依赖: mem_extremePoints, of_mem_extremePoints
-/
theorem iff_mem_extremePoints [IsProbabilityMeasure μ] :
    Ergodic f μ ↔ μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} :=
  ⟨mem_extremePoints, of_mem_extremePoints⟩

end Ergodic
