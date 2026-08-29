/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Exhaustion
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Analysis.LConvolution

/-!
# Measure with a given density with respect to another measure

For a measure `μ` on `α` and a function `f : α → ℝ≥0∞`, we define a new measure `μ.withDensity f`.
On a measurable set `s`, that measure has value `∫⁻ a in s, f a ∂μ`.

An important result about `withDensity` is the Radon-Nikodym theorem. It states that, given measures
`μ, ν`, if `HaveLebesgueDecomposition μ ν` then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that
`μ = ν.withDensity f`.
See `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`.

-/

@[expose] public section

open Set hiding restrict restrict_apply

open Filter ENNReal NNReal MeasureTheory.Measure

namespace MeasureTheory

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}

/-- Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the
measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`. -/
noncomputable
/--
Definition of `Measure.withDensity` / `Measure.withDensity` 的定义

English:
definition Measure.withDensity
  signature: {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞)
  body: Measure.ofMeasurable (fun s _ => ∫⁻ a in s, f a ∂μ) (by simp) fun _ hs hd =>
    lintegral_iUnion hs hd _

@[simp]

中文:
定义 测度.withDensity
  签名: {m : 可测空间 α} (μ : 测度 α) (f : α -> 实数>=0∞)
  定义体: Measure.ofMeasurable (fun s _ => ∫⁻ a in s, f a ∂μ) (by simp) fun _ hs hd =>
    lintegral_iUnion hs hd _

@[simp]

Depends on / 依赖: Measure, Measure.ofMeasurable, lintegral_iUnion, ofMeasurable
-/
def Measure.withDensity {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ a in s, f a ∂μ) (by simp) fun _ hs hd =>
    lintegral_iUnion hs hd _

@[simp]
/--
theorem `withDensity_apply` / 定理 `withDensity_apply`

English:
theorem withDensity_apply
  given: (f : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s)
  proof: Measure.ofMeasurable_apply s hs

中文:
定理 withDensity_apply
  条件: (f : α -> 实数>=0∞) {s : 集合 α} (hs : 可测集 s)
  证明: Measure.ofMeasurable_apply s hs

Depends on / 依赖: Measure, Measure.ofMeasurable_apply, ofMeasurable_apply
-/
theorem withDensity_apply (f : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity f s = ∫⁻ a in s, f a ∂μ :=
  Measure.ofMeasurable_apply s hs

/--
theorem `withDensity_apply_le` / 定理 `withDensity_apply_le`

English:
theorem withDensity_apply_le
  given: (f : α -> Real>=0∞) (s : Set α)
  proof: by
  let t := toMeasurable (μ.withDensity f) s
  calc
  ∫⁻ a in s, f a ∂μ <= ∫⁻ a in t, f a ∂μ :=
    lintegral_mono_set (subset_toMeasurable (withDensity μ f) s)
  _ = μ.withDensity f t :=
    (withDensity_apply f (measurableSet_toMeasurable (withDensity μ f) s)).symm
  _ = μ.withDensity f s := measure_toMeasurable s

中文:
定理 withDensity_apply_le
  条件: (f : α -> 实数>=0∞) (s : 集合 α)
  证明: by
  let t := toMeasurable (μ.withDensity f) s
  calc
  ∫⁻ a in s, f a ∂μ <= ∫⁻ a in t, f a ∂μ :=
    lintegral_mono_set (subset_toMeasurable (withDensity μ f) s)
  _ = μ.withDensity f t :=
    (withDensity_apply f (measurableSet_toMeasurable (withDensity μ f) s)).symm
  _ = μ.withDensity f s := measure_toMeasurable s

Depends on / 依赖: lintegral_mono_set, measurableSet_toMeasurable, measure_toMeasurable, subset_toMeasurable, toMeasurable, withDensity, withDensity_apply
-/
theorem withDensity_apply_le (f : α -> Real>=0∞) (s : Set α) :
    ∫⁻ a in s, f a ∂μ <= μ.withDensity f s := by
  let t := toMeasurable (μ.withDensity f) s
  calc
  ∫⁻ a in s, f a ∂μ <= ∫⁻ a in t, f a ∂μ :=
    lintegral_mono_set (subset_toMeasurable (withDensity μ f) s)
  _ = μ.withDensity f t :=
    (withDensity_apply f (measurableSet_toMeasurable (withDensity μ f) s)).symm
  _ = μ.withDensity f s := measure_toMeasurable s



/--
theorem `withDensity_apply'` / 定理 `withDensity_apply'`

English:
theorem withDensity_apply'
  given: [SFinite μ] (f : α -> Real>=0∞) (s : Set α)
  proof: by
  apply le_antisymm ?_ (withDensity_apply_le f s)
  let t := toMeasurable μ s
  calc
  μ.withDensity f s <= μ.withDensity f t := measure_mono (subset_toMeasurable μ s)
  _ = ∫⁻ a in t, f a ∂μ := withDensity_apply f (measurableSet_toMeasurable μ s)
  _ = ∫⁻ a in s, f a ∂μ := by congr 1; exact restrict_toMeasurable_of_sFinite s

@[simp]

中文:
定理 withDensity_apply'
  条件: [SFinite μ] (f : α -> 实数>=0∞) (s : 集合 α)
  证明: by
  apply le_antisymm ?_ (withDensity_apply_le f s)
  let t := toMeasurable μ s
  calc
  μ.withDensity f s <= μ.withDensity f t := measure_mono (subset_toMeasurable μ s)
  _ = ∫⁻ a in t, f a ∂μ := withDensity_apply f (measurableSet_toMeasurable μ s)
  _ = ∫⁻ a in s, f a ∂μ := by congr 1; exact restrict_toMeasurable_of_sFinite s

@[simp]

Depends on / 依赖: le_antisymm, measurableSet_toMeasurable, measure_mono, restrict_toMeasurable_of_sFinite, subset_toMeasurable, toMeasurable, withDensity, withDensity_apply, withDensity_apply_le
-/
theorem withDensity_apply' [SFinite μ] (f : α -> Real>=0∞) (s : Set α) :
    μ.withDensity f s = ∫⁻ a in s, f a ∂μ := by
  apply le_antisymm ?_ (withDensity_apply_le f s)
  let t := toMeasurable μ s
  calc
  μ.withDensity f s <= μ.withDensity f t := measure_mono (subset_toMeasurable μ s)
  _ = ∫⁻ a in t, f a ∂μ := withDensity_apply f (measurableSet_toMeasurable μ s)
  _ = ∫⁻ a in s, f a ∂μ := by congr 1; exact restrict_toMeasurable_of_sFinite s

@[simp]
/--
lemma `withDensity_zero_left` / 引理 `withDensity_zero_left`

English:
lemma withDensity_zero_left
  given: (f : α -> Real>=0∞)
  statement: (0 : Measure α).withDensity f = 0
  proof: by
  ext s hs
  rw [withDensity_apply _ hs]
  simp

中文:
引理 withDensity_zero_left
  条件: (f : α -> 实数>=0∞)
  结论: (0 : 测度 α).withDensity f = 0
  证明: by
  ext s hs
  rw [withDensity_apply _ hs]
  simp

Depends on / 依赖: withDensity_apply
-/
lemma withDensity_zero_left (f : α -> Real>=0∞) : (0 : Measure α).withDensity f = 0 := by
  ext s hs
  rw [withDensity_apply _ hs]
  simp

/--
theorem `withDensity_congr_ae` / 定理 `withDensity_congr_ae`

English:
theorem withDensity_congr_ae
  given: {f g : α -> Real>=0∞} (h : f =ᵐ[μ] g)
  proof: by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
  exact lintegral_congr_ae (ae_restrict_of_ae h)

中文:
定理 withDensity_congr_ae
  条件: {f g : α -> 实数>=0∞} (h : f =ᵐ[μ] g)
  证明: by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
  exact lintegral_congr_ae (ae_restrict_of_ae h)

Depends on / 依赖: Measure, Measure.ext, ae_restrict_of_ae, lintegral_congr_ae, withDensity_apply
-/
theorem withDensity_congr_ae {f g : α -> Real>=0∞} (h : f =ᵐ[μ] g) :
    μ.withDensity f = μ.withDensity g := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
  exact lintegral_congr_ae (ae_restrict_of_ae h)

/--
lemma `withDensity_mono` / 引理 `withDensity_mono`

English:
lemma withDensity_mono
  given: {f g : α -> Real>=0∞} (hfg : f <=ᵐ[μ] g)
  proof: by
  refine le_iff.2 fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
  refine setLIntegral_mono_ae' hs ?_
  filter_upwards [hfg] with x h_le using fun _ => h_le

中文:
引理 withDensity_mono
  条件: {f g : α -> 实数>=0∞} (hfg : f <=ᵐ[μ] g)
  证明: by
  refine le_iff.2 fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
  refine setLIntegral_mono_ae' hs ?_
  filter_upwards [hfg] with x h_le using fun _ => h_le

Depends on / 依赖: filter_upwards, h_le, le_iff, setLIntegral_mono_ae, withDensity_apply
-/
lemma withDensity_mono {f g : α -> Real>=0∞} (hfg : f <=ᵐ[μ] g) :
    μ.withDensity f <= μ.withDensity g := by
  refine le_iff.2 fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
  refine setLIntegral_mono_ae' hs ?_
  filter_upwards [hfg] with x h_le using fun _ => h_le

/--
theorem `withDensity_add_left` / 定理 `withDensity_add_left`

English:
theorem withDensity_add_left
  given: {f : α -> Real>=0∞} (hf : Measurable f) (g : α -> Real>=0∞)
  proof: by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [Measure.add_apply]; rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]; rw [← lintegral_add_left hf]
  simp only [Pi.add_apply]

中文:
定理 withDensity_add_left
  条件: {f : α -> 实数>=0∞} (hf : 可测 f) (g : α -> 实数>=0∞)
  证明: by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [Measure.add_apply]; rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]; rw [← lintegral_add_left hf]
  simp only [Pi.add_apply]

Depends on / 依赖: Measure, Measure.add_apply, Measure.ext, Pi.add_apply, add_apply, lintegral_add_left, withDensity_apply
-/
theorem withDensity_add_left {f : α -> Real>=0∞} (hf : Measurable f) (g : α -> Real>=0∞) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [Measure.add_apply]; rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]; rw [← lintegral_add_left hf]
  simp only [Pi.add_apply]

/--
theorem `withDensity_add_right` / 定理 `withDensity_add_right`

English:
theorem withDensity_add_right
  given: (f : α -> Real>=0∞) {g : α -> Real>=0∞} (hg : Measurable g)
  proof: by
  simpa only [add_comm] using withDensity_add_left hg f

中文:
定理 withDensity_add_right
  条件: (f : α -> 实数>=0∞) {g : α -> 实数>=0∞} (hg : 可测 g)
  证明: by
  simpa only [add_comm] using withDensity_add_left hg f

Depends on / 依赖: add_comm, withDensity_add_left
-/
theorem withDensity_add_right (f : α -> Real>=0∞) {g : α -> Real>=0∞} (hg : Measurable g) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  simpa only [add_comm] using withDensity_add_left hg f

/--
theorem `withDensity_add_measure` / 定理 `withDensity_add_measure`

English:
theorem withDensity_add_measure
  given: {m : MeasurableSpace α} (μ ν : Measure α) (f : α -> Real>=0∞)
  proof: by
  ext1 s hs
  simp only [withDensity_apply f hs, restrict_add, lintegral_add_measure, Measure.add_apply]

中文:
定理 withDensity_add_measure
  条件: {m : 可测空间 α} (μ ν : 测度 α) (f : α -> 实数>=0∞)
  证明: by
  ext1 s hs
  simp only [withDensity_apply f hs, restrict_add, lintegral_add_measure, Measure.add_apply]

Depends on / 依赖: Measure, Measure.add_apply, add_apply, lintegral_add_measure, restrict_add, withDensity_apply
-/
theorem withDensity_add_measure {m : MeasurableSpace α} (μ ν : Measure α) (f : α -> Real>=0∞) :
    (μ + ν).withDensity f = μ.withDensity f + ν.withDensity f := by
  ext1 s hs
  simp only [withDensity_apply f hs, restrict_add, lintegral_add_measure, Measure.add_apply]

/--
theorem `withDensity_sum` / 定理 `withDensity_sum`

English:
theorem withDensity_sum
  given: {ι : Type*} {m : MeasurableSpace α} (μ : ι -> Measure α) (f : α -> Real>=0∞)
  proof: by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply f hs, restrict_sum μ hs, lintegral_sum_measure]

中文:
定理 withDensity_sum
  条件: {ι : 类型} {m : 可测空间 α} (μ : ι -> 测度 α) (f : α -> 实数>=0∞)
  证明: by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply f hs, restrict_sum μ hs, lintegral_sum_measure]

Depends on / 依赖: lintegral_sum_measure, restrict_sum, simp_rw, sum_apply, withDensity_apply
-/
theorem withDensity_sum {ι : Type*} {m : MeasurableSpace α} (μ : ι -> Measure α) (f : α -> Real>=0∞) :
    (sum μ).withDensity f = sum fun n => (μ n).withDensity f := by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply f hs, restrict_sum μ hs, lintegral_sum_measure]

/--
theorem `withDensity_smul` / 定理 `withDensity_smul`

English:
theorem withDensity_smul
  given: (r : Real>=0∞) {f : α -> Real>=0∞} (hf : Measurable f)
  proof: by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [Measure.coe_smul]; rw [Pi.smul_apply]; rw [withDensity_apply _ hs]; rw [smul_eq_mul]; rw [← lintegral_const_mul r hf]
  simp only [Pi.smul_apply, smul_eq_mul]

中文:
定理 withDensity_smul
  条件: (r : 实数>=0∞) {f : α -> 实数>=0∞} (hf : 可测 f)
  证明: by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [Measure.coe_smul]; rw [Pi.smul_apply]; rw [withDensity_apply _ hs]; rw [smul_eq_mul]; rw [← lintegral_const_mul r hf]
  simp only [Pi.smul_apply, smul_eq_mul]

Depends on / 依赖: Measure, Measure.coe_smul, Measure.ext, Pi.smul_apply, coe_smul, lintegral_const_mul, smul_apply, smul_eq_mul, withDensity_apply
-/
theorem withDensity_smul (r : Real>=0∞) {f : α -> Real>=0∞} (hf : Measurable f) :
    μ.withDensity (r • f) = r • μ.withDensity f := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [Measure.coe_smul]; rw [Pi.smul_apply]; rw [withDensity_apply _ hs]; rw [smul_eq_mul]; rw [← lintegral_const_mul r hf]
  simp only [Pi.smul_apply, smul_eq_mul]

/--
theorem `withDensity_smul'` / 定理 `withDensity_smul'`

English:
theorem withDensity_smul'
  given: (r : Real>=0∞) (f : α -> Real>=0∞) (hr : r != ∞)
  proof: by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [Measure.coe_smul]; rw [Pi.smul_apply]; rw [withDensity_apply _ hs]; rw [smul_eq_mul]; rw [← lintegral_const_mul' r f hr]
  simp only [Pi.smul_apply, smul_eq_mul]

中文:
定理 withDensity_smul'
  条件: (r : 实数>=0∞) (f : α -> 实数>=0∞) (hr : r != ∞)
  证明: by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [Measure.coe_smul]; rw [Pi.smul_apply]; rw [withDensity_apply _ hs]; rw [smul_eq_mul]; rw [← lintegral_const_mul' r f hr]
  simp only [Pi.smul_apply, smul_eq_mul]

Depends on / 依赖: Measure, Measure.coe_smul, Measure.ext, Pi.smul_apply, coe_smul, lintegral_const_mul, smul_apply, smul_eq_mul, withDensity_apply
-/
theorem withDensity_smul' (r : Real>=0∞) (f : α -> Real>=0∞) (hr : r != ∞) :
    μ.withDensity (r • f) = r • μ.withDensity f := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]; rw [Measure.coe_smul]; rw [Pi.smul_apply]; rw [withDensity_apply _ hs]; rw [smul_eq_mul]; rw [← lintegral_const_mul' r f hr]
  simp only [Pi.smul_apply, smul_eq_mul]

/--
theorem `withDensity_smul_measure` / 定理 `withDensity_smul_measure`

English:
theorem withDensity_smul_measure
  given: (r : Real>=0∞) (f : α -> Real>=0∞)
  proof: by
  ext s hs
  simp [withDensity_apply, hs]

中文:
定理 withDensity_smul_measure
  条件: (r : 实数>=0∞) (f : α -> 实数>=0∞)
  证明: by
  ext s hs
  simp [withDensity_apply, hs]

Depends on / 依赖: withDensity_apply
-/
theorem withDensity_smul_measure (r : Real>=0∞) (f : α -> Real>=0∞) :
    (r • μ).withDensity f = r • μ.withDensity f := by
  ext s hs
  simp [withDensity_apply, hs]

/--
theorem `isFiniteMeasure_withDensity` / 定理 `isFiniteMeasure_withDensity`

English:
theorem isFiniteMeasure_withDensity
  given: {f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞)
  proof: { measure_univ_lt_top := by
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lt_top_iff_ne_top] }

中文:
定理 isFiniteMeasure_withDensity
  条件: {f : α -> 实数>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞)
  证明: { measure_univ_lt_top := by
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lt_top_iff_ne_top] }

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, lt_top_iff_ne_top, measure_univ_lt_top, restrict_univ, withDensity_apply
-/
theorem isFiniteMeasure_withDensity {f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞) :
    IsFiniteMeasure (μ.withDensity f) :=
  { measure_univ_lt_top := by
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lt_top_iff_ne_top] }

/--
theorem `withDensity_absolutelyContinuous` / 定理 `withDensity_absolutelyContinuous`

English:
theorem withDensity_absolutelyContinuous
  given: {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞)
  proof: by
  refine AbsolutelyContinuous.mk fun s hs₁ hs₂ => ?_
  rw [withDensity_apply _ hs₁]
  exact setLIntegral_measure_zero _ _ hs₂

中文:
定理 withDensity_absolutelyContinuous
  条件: {m : 可测空间 α} (μ : 测度 α) (f : α -> 实数>=0∞)
  证明: by
  refine AbsolutelyContinuous.mk fun s hs₁ hs₂ => ?_
  rw [withDensity_apply _ hs₁]
  exact setLIntegral_measure_zero _ _ hs₂

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, setLIntegral_measure_zero, withDensity_apply
-/
theorem withDensity_absolutelyContinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) :
    μ.withDensity f ≪ μ := by
  refine AbsolutelyContinuous.mk fun s hs₁ hs₂ => ?_
  rw [withDensity_apply _ hs₁]
  exact setLIntegral_measure_zero _ _ hs₂

/--
theorem `withDensity_apply₀` / 定理 `withDensity_apply₀`

English:
theorem withDensity_apply₀
  given: (f : α -> Real>=0∞) {s : Set α} (hs : NullMeasurableSet s μ)
  proof: by
  let t := toMeasurable μ s
  have A : ∫⁻ a in t, f a ∂μ = ∫⁻ a in s, f a ∂μ :=
    setLIntegral_congr hs.toMeasurable_ae_eq
  have B : μ.withDensity f t = μ.withDensity f s :=
    measure_congr (withDensity_absolutelyContinuous μ f hs.toMeasurable_ae_eq)
  rw [← A]; rw [← B]
  exact withDensity_apply _ (measurableSet_toMeasurable μ s)

中文:
定理 withDensity_apply₀
  条件: (f : α -> 实数>=0∞) {s : 集合 α} (hs : NullMeasurableSet s μ)
  证明: by
  let t := toMeasurable μ s
  have A : ∫⁻ a in t, f a ∂μ = ∫⁻ a in s, f a ∂μ :=
    setLIntegral_congr hs.toMeasurable_ae_eq
  have B : μ.withDensity f t = μ.withDensity f s :=
    measure_congr (withDensity_absolutelyContinuous μ f hs.toMeasurable_ae_eq)
  rw [← A]; rw [← B]
  exact withDensity_apply _ (measurableSet_toMeasurable μ s)

Depends on / 依赖: hs.toMeasurable_ae_eq, measurableSet_toMeasurable, measure_congr, setLIntegral_congr, toMeasurable, toMeasurable_ae_eq, withDensity, withDensity_absolutelyContinuous, withDensity_apply
-/
theorem withDensity_apply₀ (f : α -> Real>=0∞) {s : Set α} (hs : NullMeasurableSet s μ) :
    μ.withDensity f s = ∫⁻ a in s, f a ∂μ := by
  let t := toMeasurable μ s
  have A : ∫⁻ a in t, f a ∂μ = ∫⁻ a in s, f a ∂μ :=
    setLIntegral_congr hs.toMeasurable_ae_eq
  have B : μ.withDensity f t = μ.withDensity f s :=
    measure_congr (withDensity_absolutelyContinuous μ f hs.toMeasurable_ae_eq)
  rw [← A]; rw [← B]
  exact withDensity_apply _ (measurableSet_toMeasurable μ s)

/--
Instance `nullSingletonClass_withDensity` / 实例 `nullSingletonClass_withDensity`

English:
instance nullSingletonClass_withDensity
  signature: [NullSingletonClass μ] (f : α -> Real>=0∞)
  body: withDensity_absolutelyContinuous μ f (measure_singleton _)

@[deprecated (since := "2026-06-09")]
alias noAtoms_withDensity := nullSingletonClass_withDensity

@[simp]

中文:
实例 nullSingletonClass_withDensity
  签名: [NullSingleton类 μ] (f : α -> 实数>=0∞)
  定义体: withDensity_absolutelyContinuous μ f (measure_singleton _)

@[deprecated (since := "2026-06-09")]
alias noAtoms_withDensity := nullSingletonClass_withDensity

@[simp]

Depends on / 依赖: measure_singleton, withDensity_absolutelyContinuous
-/
instance nullSingletonClass_withDensity [NullSingletonClass μ] (f : α -> Real>=0∞) :
    NullSingletonClass (μ.withDensity f) where
  measure_singleton _ := withDensity_absolutelyContinuous μ f (measure_singleton _)

@[deprecated (since := "2026-06-09")]
alias noAtoms_withDensity := nullSingletonClass_withDensity

@[simp]
/--
theorem `withDensity_zero` / 定理 `withDensity_zero`

English:
theorem withDensity_zero
  statement: μ.withDensity 0 = 0
  proof: by
  ext1 s hs
  simp [withDensity_apply _ hs]

@[simp]

中文:
定理 withDensity_zero
  结论: μ.withDensity 0 = 0
  证明: by
  ext1 s hs
  simp [withDensity_apply _ hs]

@[simp]

Depends on / 依赖: withDensity_apply
-/
theorem withDensity_zero : μ.withDensity 0 = 0 := by
  ext1 s hs
  simp [withDensity_apply _ hs]

@[simp]
/--
theorem `withDensity_one` / 定理 `withDensity_one`

English:
theorem withDensity_one
  statement: μ.withDensity 1 = μ
  proof: by
  ext1 s hs
  simp [withDensity_apply _ hs]

@[simp]

中文:
定理 withDensity_one
  结论: μ.withDensity 1 = μ
  证明: by
  ext1 s hs
  simp [withDensity_apply _ hs]

@[simp]

Depends on / 依赖: withDensity_apply
-/
theorem withDensity_one : μ.withDensity 1 = μ := by
  ext1 s hs
  simp [withDensity_apply _ hs]

@[simp]
/--
theorem `withDensity_const` / 定理 `withDensity_const`

English:
theorem withDensity_const
  given: (c : Real>=0∞)
  statement: μ.withDensity (fun _ => c) = c • μ
  proof: by
  ext1 s hs
  simp [withDensity_apply _ hs]

中文:
定理 withDensity_const
  条件: (c : 实数>=0∞)
  结论: μ.withDensity (fun _ => c) = c • μ
  证明: by
  ext1 s hs
  simp [withDensity_apply _ hs]

Depends on / 依赖: withDensity_apply
-/
theorem withDensity_const (c : Real>=0∞) : μ.withDensity (fun _ => c) = c • μ := by
  ext1 s hs
  simp [withDensity_apply _ hs]

/--
theorem `withDensity_tsum` / 定理 `withDensity_tsum`

English:
theorem withDensity_tsum
  given: {ι : Type*} [Countable ι] {f : ι -> α -> Real>=0∞} (h : forall i, Measurable (f i))
  proof: by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply _ hs]
  change ∫⁻ x in s, (∑' n, f n) x ∂μ = ∑' i, ∫⁻ x, f i x ∂μ.restrict s
  rw [← lintegral_tsum fun i => (h i).aemeasurable]
  exact lintegral_congr fun x => tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)

中文:
定理 withDensity_tsum
  条件: {ι : 类型} [可数 ι] {f : ι -> α -> 实数>=0∞} (h : 对任意 i, 可测 (f i))
  证明: by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply _ hs]
  change ∫⁻ x in s, (∑' n, f n) x ∂μ = ∑' i, ∫⁻ x, f i x ∂μ.restrict s
  rw [← lintegral_tsum fun i => (h i).aemeasurable]
  exact lintegral_congr fun x => tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)

Depends on / 依赖: ENNReal, ENNReal.summable, Pi.summable, aemeasurable, lintegral_congr, lintegral_tsum, restrict, simp_rw, sum_apply, summable, tsum_apply, withDensity_apply
-/
theorem withDensity_tsum {ι : Type*} [Countable ι] {f : ι -> α -> Real>=0∞} (h : forall i, Measurable (f i)) :
    μ.withDensity (∑' n, f n) = sum fun n => μ.withDensity (f n) := by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply _ hs]
  change ∫⁻ x in s, (∑' n, f n) x ∂μ = ∑' i, ∫⁻ x, f i x ∂μ.restrict s
  rw [← lintegral_tsum fun i => (h i).aemeasurable]
  exact lintegral_congr fun x => tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)

/--
theorem `withDensity_indicator` / 定理 `withDensity_indicator`

English:
theorem withDensity_indicator
  given: {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞)
  proof: by
  ext1 t ht
  rw [withDensity_apply _ ht]; rw [lintegral_indicator hs]; rw [restrict_comm hs]; rw [←
    withDensity_apply _ ht]

中文:
定理 withDensity_indicator
  条件: {s : 集合 α} (hs : 可测集 s) (f : α -> 实数>=0∞)
  证明: by
  ext1 t ht
  rw [withDensity_apply _ ht]; rw [lintegral_indicator hs]; rw [restrict_comm hs]; rw [←
    withDensity_apply _ ht]

Depends on / 依赖: lintegral_indicator, restrict_comm, withDensity_apply
-/
theorem withDensity_indicator {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞) :
    μ.withDensity (s.indicator f) = (μ.restrict s).withDensity f := by
  ext1 t ht
  rw [withDensity_apply _ ht]; rw [lintegral_indicator hs]; rw [restrict_comm hs]; rw [←
    withDensity_apply _ ht]

/--
theorem `withDensity_indicator_one` / 定理 `withDensity_indicator_one`

English:
theorem withDensity_indicator_one
  given: {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [withDensity_indicator hs]; rw [withDensity_one]

中文:
定理 withDensity_indicator_one
  条件: {s : 集合 α} (hs : 可测集 s)
  证明: by
  rw [withDensity_indicator hs]; rw [withDensity_one]

Depends on / 依赖: withDensity_indicator, withDensity_one
-/
theorem withDensity_indicator_one {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity (s.indicator 1) = μ.restrict s := by
  rw [withDensity_indicator hs]; rw [withDensity_one]

/--
theorem `withDensity_ofReal_mutuallySingular` / 定理 `withDensity_ofReal_mutuallySingular`

English:
theorem withDensity_ofReal_mutuallySingular
  given: {f : α -> Real} (hf : Measurable f)
  proof: by
  set S : Set α := { x | f x < 0 }
  have hS : MeasurableSet S := measurableSet_lt hf measurable_const
  refine ⟨S, hS, ?_, ?_⟩
  · rw [withDensity_apply _ hS, lintegral_eq_zero_iff hf.ennreal_ofReal, EventuallyEq]
    exact (ae_restrict_mem hS).mono fun x hx => ENNReal.ofReal_eq_zero.2 (le_of_lt hx)
  · rw [withDensity_apply _ hS.compl, lintegral_eq_zero_iff hf.fun_neg.ennreal_ofReal, EventuallyEq]
    exact
      (ae_restrict_mem hS.compl).mono fun x hx =>
        ENNReal.ofReal_eq_zero.2 (not_lt.1 <| mt neg_pos.1 hx)

中文:
定理 withDensity_of实数_mutuallySingular
  条件: {f : α -> 实数} (hf : 可测 f)
  证明: by
  set S : Set α := { x | f x < 0 }
  have hS : MeasurableSet S := measurableSet_lt hf measurable_const
  refine ⟨S, hS, ?_, ?_⟩
  · rw [withDensity_apply _ hS, lintegral_eq_zero_iff hf.ennreal_ofReal, EventuallyEq]
    exact (ae_restrict_mem hS).mono fun x hx => ENNReal.ofReal_eq_zero.2 (le_of_lt hx)
  · rw [withDensity_apply _ hS.compl, lintegral_eq_zero_iff hf.fun_neg.ennreal_ofReal, EventuallyEq]
    exact
      (ae_restrict_mem hS.compl).mono fun x hx =>
        ENNReal.ofReal_eq_zero.2 (not_lt.1 <| mt neg_pos.1 hx)

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, EventuallyEq, MeasurableSet, ae_restrict_mem, ennreal_ofReal, fun_neg, hS.compl, hf.ennreal_ofReal, hf.fun_neg.ennreal_ofReal, le_of_lt, lintegral_eq_zero_iff, measurableSet_lt, measurable_const, neg_pos, not_lt, ofReal_eq_zero, withDensity_apply
-/
theorem withDensity_ofReal_mutuallySingular {f : α -> Real} (hf : Measurable f) :
    (μ.withDensity fun x => ENNReal.ofReal <| f x) ⟂ₘ
μ.withDensity fun x => ENNReal.ofReal -f x := by
  set S : Set α := { x | f x < 0 }
  have hS : MeasurableSet S := measurableSet_lt hf measurable_const
  refine ⟨S, hS, ?_, ?_⟩
  · rw [withDensity_apply _ hS, lintegral_eq_zero_iff hf.ennreal_ofReal, EventuallyEq]
    exact (ae_restrict_mem hS).mono fun x hx => ENNReal.ofReal_eq_zero.2 (le_of_lt hx)
  · rw [withDensity_apply _ hS.compl, lintegral_eq_zero_iff hf.fun_neg.ennreal_ofReal, EventuallyEq]
    exact
      (ae_restrict_mem hS.compl).mono fun x hx =>
        ENNReal.ofReal_eq_zero.2 (not_lt.1 <| mt neg_pos.1 hx)

/--
theorem `restrict_withDensity` / 定理 `restrict_withDensity`

English:
theorem restrict_withDensity
  given: {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞)
  proof: by
  ext1 t ht
  rw [restrict_apply ht]; rw [withDensity_apply _ ht]; rw [withDensity_apply _ (ht.inter hs)]; rw [restrict_restrict ht]

中文:
定理 restrict_withDensity
  条件: {s : 集合 α} (hs : 可测集 s) (f : α -> 实数>=0∞)
  证明: by
  ext1 t ht
  rw [restrict_apply ht]; rw [withDensity_apply _ ht]; rw [withDensity_apply _ (ht.inter hs)]; rw [restrict_restrict ht]

Depends on / 依赖: ht.inter, restrict_apply, restrict_restrict, withDensity_apply
-/
theorem restrict_withDensity {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞) :
    (μ.withDensity f).restrict s = (μ.restrict s).withDensity f := by
  ext1 t ht
  rw [restrict_apply ht]; rw [withDensity_apply _ ht]; rw [withDensity_apply _ (ht.inter hs)]; rw [restrict_restrict ht]

/--
theorem `restrict_withDensity'` / 定理 `restrict_withDensity'`

English:
theorem restrict_withDensity'
  given: [SFinite μ] (s : Set α) (f : α -> Real>=0∞)
  proof: by
  ext1 t ht
  rw [restrict_apply ht]; rw [withDensity_apply _ ht]; rw [withDensity_apply' _ (t inter s)]; rw [restrict_restrict ht]

中文:
定理 restrict_withDensity'
  条件: [SFinite μ] (s : 集合 α) (f : α -> 实数>=0∞)
  证明: by
  ext1 t ht
  rw [restrict_apply ht]; rw [withDensity_apply _ ht]; rw [withDensity_apply' _ (t inter s)]; rw [restrict_restrict ht]

Depends on / 依赖: restrict_apply, restrict_restrict, withDensity_apply
-/
theorem restrict_withDensity' [SFinite μ] (s : Set α) (f : α -> Real>=0∞) :
    (μ.withDensity f).restrict s = (μ.restrict s).withDensity f := by
  ext1 t ht
  rw [restrict_apply ht]; rw [withDensity_apply _ ht]; rw [withDensity_apply' _ (t inter s)]; rw [restrict_restrict ht]

/--
lemma `trim_withDensity` / 引理 `trim_withDensity`

English:
lemma trim_withDensity
  statement: {m m0 : MeasurableSpace α} {μ : Measure α}
  proof: by
  refine @Measure.ext _ m _ _ (fun s hs => ?_)
  rw [withDensity_apply _ hs]; rw [restrict_trim _ _ hs]; rw [lintegral_trim _ hf]; rw [trim_measurableSet_eq _ hs]; rw [withDensity_apply _ (hm s hs)]

中文:
引理 trim_withDensity
  结论: {m m0 : 可测空间 α} {μ : 测度 α}
  证明: by
  refine @Measure.ext _ m _ _ (fun s hs => ?_)
  rw [withDensity_apply _ hs]; rw [restrict_trim _ _ hs]; rw [lintegral_trim _ hf]; rw [trim_measurableSet_eq _ hs]; rw [withDensity_apply _ (hm s hs)]

Depends on / 依赖: Measure, Measure.ext, lintegral_trim, restrict_trim, trim_measurableSet_eq, withDensity_apply
-/
lemma trim_withDensity {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m <= m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) :
    (μ.withDensity f).trim hm = (μ.trim hm).withDensity f := by
  refine @Measure.ext _ m _ _ (fun s hs => ?_)
  rw [withDensity_apply _ hs]; rw [restrict_trim _ _ hs]; rw [lintegral_trim _ hf]; rw [trim_measurableSet_eq _ hs]; rw [withDensity_apply _ (hm s hs)]

/--
lemma `Measure.MutuallySingular.withDensity` / 引理 `Measure.MutuallySingular.withDensity`

English:
lemma Measure.MutuallySingular.withDensity
  given: {ν : Measure α} {f : α -> Real>=0∞} (h : μ ⟂ₘ ν)
  proof: MutuallySingular.mono_ac h (withDensity_absolutelyContinuous _ _) AbsolutelyContinuous.rfl

@[simp]

中文:
引理 测度.互奇异.withDensity
  条件: {ν : 测度 α} {f : α -> 实数>=0∞} (h : μ ⟂ₘ ν)
  证明: MutuallySingular.mono_ac h (withDensity_absolutelyContinuous _ _) AbsolutelyContinuous.rfl

@[simp]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl, MutuallySingular, MutuallySingular.mono_ac, mono_ac, withDensity_absolutelyContinuous
-/
lemma Measure.MutuallySingular.withDensity {ν : Measure α} {f : α -> Real>=0∞} (h : μ ⟂ₘ ν) :
    μ.withDensity f ⟂ₘ ν :=
  MutuallySingular.mono_ac h (withDensity_absolutelyContinuous _ _) AbsolutelyContinuous.rfl

@[simp]
/--
theorem `withDensity_eq_zero_iff` / 定理 `withDensity_eq_zero_iff`

English:
theorem withDensity_eq_zero_iff
  given: {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
  proof: by
  rw [← measure_univ_eq_zero]; rw [withDensity_apply _ .univ]; rw [restrict_univ]; rw [lintegral_eq_zero_iff' hf]

alias ⟨withDensity_eq_zero, _⟩ := withDensity_eq_zero_iff

中文:
定理 withDensity_eq_zero_iff
  条件: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ)
  证明: by
  rw [← measure_univ_eq_zero]; rw [withDensity_apply _ .univ]; rw [restrict_univ]; rw [lintegral_eq_zero_iff' hf]

alias ⟨withDensity_eq_zero, _⟩ := withDensity_eq_zero_iff

Depends on / 依赖: lintegral_eq_zero_iff, measure_univ_eq_zero, restrict_univ, withDensity_apply
-/
theorem withDensity_eq_zero_iff {f : α -> Real>=0∞} (hf : AEMeasurable f μ) :
    μ.withDensity f = 0 ↔ f =ᵐ[μ] 0 := by
  rw [← measure_univ_eq_zero]; rw [withDensity_apply _ .univ]; rw [restrict_univ]; rw [lintegral_eq_zero_iff' hf]

alias ⟨withDensity_eq_zero, _⟩ := withDensity_eq_zero_iff

/--
theorem `withDensity_apply_eq_zero'` / 定理 `withDensity_apply_eq_zero'`

English:
theorem withDensity_apply_eq_zero'
  given: {f : α -> Real>=0∞} {s : Set α} (hf : AEMeasurable f μ)
  proof: by
  constructor
  · intro hs
    let t := toMeasurable (μ.withDensity f) s
    apply measure_mono_null (inter_subset_inter_right _ (subset_toMeasurable (μ.withDensity f) s))
    have A : μ.withDensity f t = 0 := by rw [measure_toMeasurable, hs]
    rw [withDensity_apply f (measurableSet_toMeasurable _ s)]; rw [lintegral_eq_zero_iff' (AEMeasurable.restrict hf)]; rw [EventuallyEq]; rw [ae_restrict_iff'₀]; rw [ae_iff] at A
    swap
    · simp only [measurableSet_toMeasurable, MeasurableSet.nullMeasurableSet]
    simp only [Pi.zero_apply] at A
    convert! A using 2
    ext x
    simp only [and_comm, exists_prop, mem_inter_iff, mem_ofPred_eq,
      not_forall]
  · intro hs
    let t := toMeasurable μ ({ x | f x != 0 } inter s)
    have A : s subseteq t union { x | f x = 0 } := by
      intro x hx
      rcases eq_or_ne (f x) 0 with (fx | fx)
      · simp only [fx, mem_union, mem_ofPred_eq, or_true]
      · left
        apply subset_toMeasurable _ _
        exact ⟨fx, hx⟩
    apply measure_mono_null A (measure_union_null _ _)
    · apply withDensity_absolutelyContinuous
      rwa [measure_toMeasurable]
    rcases hf with ⟨g, hg, hfg⟩
    have t : {x | f x = 0} =ᵐ[μ.withDensity f] {x | g x = 0} := by
      apply withDensity_absolutelyContinuous
      filter_upwards [hfg] with a ha
      rw [eq_iff_iff]
      exact ⟨fun h => by rw [h] at ha; exact ha.symm,
             fun h => by rw [h] at ha; exact ha⟩
    rw [measure_congr t]; rw [withDensity_congr_ae hfg]
    have M : MeasurableSet { x : α | g x = 0 } := hg (measurableSet_singleton _)
    rw [withDensity_apply _ M]; rw [lintegral_eq_zero_iff hg]
    filter_upwards [ae_restrict_mem M]
    simp only [imp_self, Pi.zero_apply, imp_true_iff]

中文:
定理 withDensity_apply_eq_zero'
  条件: {f : α -> 实数>=0∞} {s : 集合 α} (hf : 几乎处处可测 f μ)
  证明: by
  constructor
  · intro hs
    let t := toMeasurable (μ.withDensity f) s
    apply measure_mono_null (inter_subset_inter_right _ (subset_toMeasurable (μ.withDensity f) s))
    have A : μ.withDensity f t = 0 := by rw [measure_toMeasurable, hs]
    rw [withDensity_apply f (measurableSet_toMeasurable _ s)]; rw [lintegral_eq_zero_iff' (AEMeasurable.restrict hf)]; rw [EventuallyEq]; rw [ae_restrict_iff'₀]; rw [ae_iff] at A
    swap
    · simp only [measurableSet_toMeasurable, MeasurableSet.nullMeasurableSet]
    simp only [Pi.zero_apply] at A
    convert! A using 2
    ext x
    simp only [and_comm, exists_prop, mem_inter_iff, mem_ofPred_eq,
      not_forall]
  · intro hs
    let t := toMeasurable μ ({ x | f x != 0 } inter s)
    have A : s subseteq t union { x | f x = 0 } := by
      intro x hx
      rcases eq_or_ne (f x) 0 with (fx | fx)
      · simp only [fx, mem_union, mem_ofPred_eq, or_true]
      · left
        apply subset_toMeasurable _ _
        exact ⟨fx, hx⟩
    apply measure_mono_null A (measure_union_null _ _)
    · apply withDensity_absolutelyContinuous
      rwa [measure_toMeasurable]
    rcases hf with ⟨g, hg, hfg⟩
    have t : {x | f x = 0} =ᵐ[μ.withDensity f] {x | g x = 0} := by
      apply withDensity_absolutelyContinuous
      filter_upwards [hfg] with a ha
      rw [eq_iff_iff]
      exact ⟨fun h => by rw [h] at ha; exact ha.symm,
             fun h => by rw [h] at ha; exact ha⟩
    rw [measure_congr t]; rw [withDensity_congr_ae hfg]
    have M : MeasurableSet { x : α | g x = 0 } := hg (measurableSet_singleton _)
    rw [withDensity_apply _ M]; rw [lintegral_eq_zero_iff hg]
    filter_upwards [ae_restrict_mem M]
    simp only [imp_self, Pi.zero_apply, imp_true_iff]

Depends on / 依赖: AEMeasurable, AEMeasurable.restrict, EventuallyEq, MeasurableSet, MeasurableSet.nullMeasurableSet, Pi.ze, ae_iff, ae_restrict_iff, inter_subset_inter_right, lintegral_eq_zero_iff, measurableSet_toMeasurable, measure_mono_null, measure_toMeasurable, nullMeasurableSet, restrict, subset_toMeasurable, toMeasurable, withDensity, withDensity_apply
-/
theorem withDensity_apply_eq_zero' {f : α -> Real>=0∞} {s : Set α} (hf : AEMeasurable f μ) :
    μ.withDensity f s = 0 ↔ μ ({ x | f x != 0 } inter s) = 0 := by
  constructor
  · intro hs
    let t := toMeasurable (μ.withDensity f) s
    apply measure_mono_null (inter_subset_inter_right _ (subset_toMeasurable (μ.withDensity f) s))
    have A : μ.withDensity f t = 0 := by rw [measure_toMeasurable, hs]
    rw [withDensity_apply f (measurableSet_toMeasurable _ s)]; rw [lintegral_eq_zero_iff' (AEMeasurable.restrict hf)]; rw [EventuallyEq]; rw [ae_restrict_iff'₀]; rw [ae_iff] at A
    swap
    · simp only [measurableSet_toMeasurable, MeasurableSet.nullMeasurableSet]
    simp only [Pi.zero_apply] at A
    convert! A using 2
    ext x
    simp only [and_comm, exists_prop, mem_inter_iff, mem_ofPred_eq,
      not_forall]
  · intro hs
    let t := toMeasurable μ ({ x | f x != 0 } inter s)
    have A : s subseteq t union { x | f x = 0 } := by
      intro x hx
      rcases eq_or_ne (f x) 0 with (fx | fx)
      · simp only [fx, mem_union, mem_ofPred_eq, or_true]
      · left
        apply subset_toMeasurable _ _
        exact ⟨fx, hx⟩
    apply measure_mono_null A (measure_union_null _ _)
    · apply withDensity_absolutelyContinuous
      rwa [measure_toMeasurable]
    rcases hf with ⟨g, hg, hfg⟩
    have t : {x | f x = 0} =ᵐ[μ.withDensity f] {x | g x = 0} := by
      apply withDensity_absolutelyContinuous
      filter_upwards [hfg] with a ha
      rw [eq_iff_iff]
      exact ⟨fun h => by rw [h] at ha; exact ha.symm,
             fun h => by rw [h] at ha; exact ha⟩
    rw [measure_congr t]; rw [withDensity_congr_ae hfg]
    have M : MeasurableSet { x : α | g x = 0 } := hg (measurableSet_singleton _)
    rw [withDensity_apply _ M]; rw [lintegral_eq_zero_iff hg]
    filter_upwards [ae_restrict_mem M]
    simp only [imp_self, Pi.zero_apply, imp_true_iff]

/--
theorem `withDensity_apply_eq_zero` / 定理 `withDensity_apply_eq_zero`

English:
theorem withDensity_apply_eq_zero
  given: {f : α -> Real>=0∞} {s : Set α} (hf : Measurable f)
  proof: withDensity_apply_eq_zero' hf.aemeasurable

中文:
定理 withDensity_apply_eq_zero
  条件: {f : α -> 实数>=0∞} {s : 集合 α} (hf : 可测 f)
  证明: withDensity_apply_eq_zero' hf.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable, withDensity_apply_eq_zero
-/
theorem withDensity_apply_eq_zero {f : α -> Real>=0∞} {s : Set α} (hf : Measurable f) :
    μ.withDensity f s = 0 ↔ μ ({ x | f x != 0 } inter s) = 0 :=
withDensity_apply_eq_zero' hf.aemeasurable

/--
theorem `ae_withDensity_iff'` / 定理 `ae_withDensity_iff'`

English:
theorem ae_withDensity_iff'
  given: {p : α -> Prop} {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
  proof: by
  rw [ae_iff]; rw [ae_iff]; rw [withDensity_apply_eq_zero' hf]; rw [iff_iff_eq]
  congr
  ext x
  simp only [exists_prop, mem_inter_iff, mem_ofPred_eq, not_forall]

中文:
定理 ae_withDensity_iff'
  条件: {p : α -> 命题} {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ)
  证明: by
  rw [ae_iff]; rw [ae_iff]; rw [withDensity_apply_eq_zero' hf]; rw [iff_iff_eq]
  congr
  ext x
  simp only [exists_prop, mem_inter_iff, mem_ofPred_eq, not_forall]

Depends on / 依赖: ae_iff, exists_prop, iff_iff_eq, mem_inter_iff, mem_ofPred_eq, not_forall, withDensity_apply_eq_zero
-/
theorem ae_withDensity_iff' {p : α -> Prop} {f : α -> Real>=0∞} (hf : AEMeasurable f μ) :
    (forallᵐ x ∂μ.withDensity f, p x) ↔ forallᵐ x ∂μ, f x != 0 -> p x := by
  rw [ae_iff]; rw [ae_iff]; rw [withDensity_apply_eq_zero' hf]; rw [iff_iff_eq]
  congr
  ext x
  simp only [exists_prop, mem_inter_iff, mem_ofPred_eq, not_forall]

/--
theorem `ae_withDensity_iff` / 定理 `ae_withDensity_iff`

English:
theorem ae_withDensity_iff
  given: {p : α -> Prop} {f : α -> Real>=0∞} (hf : Measurable f)
  proof: ae_withDensity_iff' hf.aemeasurable

中文:
定理 ae_withDensity_iff
  条件: {p : α -> 命题} {f : α -> 实数>=0∞} (hf : 可测 f)
  证明: ae_withDensity_iff' hf.aemeasurable

Depends on / 依赖: ae_withDensity_iff, aemeasurable, hf.aemeasurable
-/
theorem ae_withDensity_iff {p : α -> Prop} {f : α -> Real>=0∞} (hf : Measurable f) :
    (forallᵐ x ∂μ.withDensity f, p x) ↔ forallᵐ x ∂μ, f x != 0 -> p x :=
ae_withDensity_iff' hf.aemeasurable

/--
theorem `ae_withDensity_iff_ae_restrict'` / 定理 `ae_withDensity_iff_ae_restrict'`

English:
theorem ae_withDensity_iff_ae_restrict'
  statement: {p : α -> Prop} {f : α -> Real>=0∞}
  proof: by
  rw [ae_withDensity_iff' hf]; rw [ae_restrict_iff'₀]
  · simp only [mem_ofPred]
  · rcases hf with ⟨g, hg, hfg⟩
    have nonneg_eq_ae : {x | g x != 0} =ᵐ[μ] {x | f x != 0} := by
      filter_upwards [hfg] with a ha
      simp only [eq_iff_iff]
      exact ⟨fun (h : g a != 0) => by rwa [← ha] at h,
             fun (h : f a != 0) => by rwa [ha] at h⟩
    exact NullMeasurableSet.congr
      (MeasurableSet.nullMeasurableSet
 hg (measurableSet_singleton _)).compl
      nonneg_eq_ae

中文:
定理 ae_withDensity_iff_ae_restrict'
  结论: {p : α -> 命题} {f : α -> 实数>=0∞}
  证明: by
  rw [ae_withDensity_iff' hf]; rw [ae_restrict_iff'₀]
  · simp only [mem_ofPred]
  · rcases hf with ⟨g, hg, hfg⟩
    have nonneg_eq_ae : {x | g x != 0} =ᵐ[μ] {x | f x != 0} := by
      filter_upwards [hfg] with a ha
      simp only [eq_iff_iff]
      exact ⟨fun (h : g a != 0) => by rwa [← ha] at h,
             fun (h : f a != 0) => by rwa [ha] at h⟩
    exact NullMeasurableSet.congr
      (MeasurableSet.nullMeasurableSet
 hg (measurableSet_singleton _)).compl
      nonneg_eq_ae

Depends on / 依赖: MeasurableSet, MeasurableSet.nullMeasurableSet, NullMeasurableSet, NullMeasurableSet.congr, ae_restrict_iff, ae_withDensity_iff, eq_iff_iff, filter_upwards, measurableSet_singleton, mem_ofPred, nonneg_eq_ae, nullMeasurableSet
-/
theorem ae_withDensity_iff_ae_restrict' {p : α -> Prop} {f : α -> Real>=0∞}
    (hf : AEMeasurable f μ) :
    (forallᵐ x ∂μ.withDensity f, p x) ↔ forallᵐ x ∂μ.restrict { x | f x != 0 }, p x := by
  rw [ae_withDensity_iff' hf]; rw [ae_restrict_iff'₀]
  · simp only [mem_ofPred]
  · rcases hf with ⟨g, hg, hfg⟩
    have nonneg_eq_ae : {x | g x != 0} =ᵐ[μ] {x | f x != 0} := by
      filter_upwards [hfg] with a ha
      simp only [eq_iff_iff]
      exact ⟨fun (h : g a != 0) => by rwa [← ha] at h,
             fun (h : f a != 0) => by rwa [ha] at h⟩
    exact NullMeasurableSet.congr
      (MeasurableSet.nullMeasurableSet
 hg (measurableSet_singleton _)).compl
      nonneg_eq_ae

/--
theorem `ae_withDensity_iff_ae_restrict` / 定理 `ae_withDensity_iff_ae_restrict`

English:
theorem ae_withDensity_iff_ae_restrict
  given: {p : α -> Prop} {f : α -> Real>=0∞} (hf : Measurable f)
  proof: ae_withDensity_iff_ae_restrict' hf.aemeasurable

中文:
定理 ae_withDensity_iff_ae_restrict
  条件: {p : α -> 命题} {f : α -> 实数>=0∞} (hf : 可测 f)
  证明: ae_withDensity_iff_ae_restrict' hf.aemeasurable

Depends on / 依赖: ae_withDensity_iff_ae_restrict, aemeasurable, hf.aemeasurable
-/
theorem ae_withDensity_iff_ae_restrict {p : α -> Prop} {f : α -> Real>=0∞} (hf : Measurable f) :
    (forallᵐ x ∂μ.withDensity f, p x) ↔ forallᵐ x ∂μ.restrict { x | f x != 0 }, p x :=
ae_withDensity_iff_ae_restrict' hf.aemeasurable

/--
theorem `aemeasurable_withDensity_ennreal_iff'` / 定理 `aemeasurable_withDensity_ennreal_iff'`

English:
theorem aemeasurable_withDensity_ennreal_iff'
  statement: {f : α -> Real>=0}
  proof: by
  have t : exists f', Measurable f' ∧ f =ᵐ[μ] f' := hf
  rcases t with ⟨f', hf'_m, hf'_ae⟩
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet {x | f' x != 0} := hf'_m (measurableSet_singleton _).compl
    refine ⟨fun x => f' x * g' x, hf'_m.coe_nnreal_ennreal.smul g'meas, ?_⟩
    apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x != 0 }
    · rw [EventuallyEq, ae_withDensity_iff' hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg', hf'_ae] with a ha h'a h_a_nonneg
      have : (f' a : Real>=0∞) != 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h_a_nonneg
      rw [← h'a] at this ⊢
      rw [ha this]
    · rw [ae_restrict_iff' A.compl]
      filter_upwards [hf'_ae] with a ha ha_null
      have ha_null : f' a = 0 := Function.notMem_support.mp ha_null
      rw [ha_null] at ha ⊢
      rw [ha]
      simp only [ENNReal.coe_zero, zero_mul]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => ((f' x)⁻¹ : Real>=0∞) * g' x, hf'_m.coe_nnreal_ennreal.inv.smul g'meas, ?_⟩
    rw [EventuallyEq]; rw [ae_withDensity_iff' hf.coe_nnreal_ennreal]
    filter_upwards [hg', hf'_ae] with a hfga hff'a h'a
    rw [hff'a] at hfga h'a
    rw [← hfga]; rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel h'a ENNReal.coe_ne_top]; rw [one_mul]

中文:
定理 aemeasurable_withDensity_ennreal_iff'
  结论: {f : α -> 实数>=0}
  证明: by
  have t : exists f', Measurable f' ∧ f =ᵐ[μ] f' := hf
  rcases t with ⟨f', hf'_m, hf'_ae⟩
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet {x | f' x != 0} := hf'_m (measurableSet_singleton _).compl
    refine ⟨fun x => f' x * g' x, hf'_m.coe_nnreal_ennreal.smul g'meas, ?_⟩
    apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x != 0 }
    · rw [EventuallyEq, ae_withDensity_iff' hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg', hf'_ae] with a ha h'a h_a_nonneg
      have : (f' a : Real>=0∞) != 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h_a_nonneg
      rw [← h'a] at this ⊢
      rw [ha this]
    · rw [ae_restrict_iff' A.compl]
      filter_upwards [hf'_ae] with a ha ha_null
      have ha_null : f' a = 0 := Function.notMem_support.mp ha_null
      rw [ha_null] at ha ⊢
      rw [ha]
      simp only [ENNReal.coe_zero, zero_mul]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => ((f' x)⁻¹ : Real>=0∞) * g' x, hf'_m.coe_nnreal_ennreal.inv.smul g'meas, ?_⟩
    rw [EventuallyEq]; rw [ae_withDensity_iff' hf.coe_nnreal_ennreal]
    filter_upwards [hg', hf'_ae] with a hfga hff'a h'a
    rw [hff'a] at hfga h'a
    rw [← hfga]; rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel h'a ENNReal.coe_ne_top]; rw [one_mul]

Depends on / 依赖: EventuallyEq, Measurable, MeasurableSet, _m.coe_nnreal_ennreal.smul, ae_of_ae_restrict_of_ae_restrict_compl, ae_restrict_iff, ae_withDensity_iff, coe_nnreal_ennreal, filter_upwards, h_a_nonneg, hf.coe_nnreal_ennreal, measurableSet_singleton
-/
theorem aemeasurable_withDensity_ennreal_iff' {f : α -> Real>=0}
    (hf : AEMeasurable f μ) {g : α -> Real>=0∞} :
    AEMeasurable g (μ.withDensity fun x => (f x : Real>=0∞)) ↔
      AEMeasurable (fun x => (f x : Real>=0∞) * g x) μ := by
  have t : exists f', Measurable f' ∧ f =ᵐ[μ] f' := hf
  rcases t with ⟨f', hf'_m, hf'_ae⟩
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet {x | f' x != 0} := hf'_m (measurableSet_singleton _).compl
    refine ⟨fun x => f' x * g' x, hf'_m.coe_nnreal_ennreal.smul g'meas, ?_⟩
    apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x != 0 }
    · rw [EventuallyEq, ae_withDensity_iff' hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg', hf'_ae] with a ha h'a h_a_nonneg
      have : (f' a : Real>=0∞) != 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h_a_nonneg
      rw [← h'a] at this ⊢
      rw [ha this]
    · rw [ae_restrict_iff' A.compl]
      filter_upwards [hf'_ae] with a ha ha_null
      have ha_null : f' a = 0 := Function.notMem_support.mp ha_null
      rw [ha_null] at ha ⊢
      rw [ha]
      simp only [ENNReal.coe_zero, zero_mul]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => ((f' x)⁻¹ : Real>=0∞) * g' x, hf'_m.coe_nnreal_ennreal.inv.smul g'meas, ?_⟩
    rw [EventuallyEq]; rw [ae_withDensity_iff' hf.coe_nnreal_ennreal]
    filter_upwards [hg', hf'_ae] with a hfga hff'a h'a
    rw [hff'a] at hfga h'a
    rw [← hfga]; rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel h'a ENNReal.coe_ne_top]; rw [one_mul]

/--
theorem `aemeasurable_withDensity_ennreal_iff` / 定理 `aemeasurable_withDensity_ennreal_iff`

English:
theorem aemeasurable_withDensity_ennreal_iff
  given: {f : α -> Real>=0} (hf : Measurable f) {g : α -> Real>=0∞}
  proof: aemeasurable_withDensity_ennreal_iff' hf.aemeasurable

中文:
定理 aemeasurable_withDensity_ennreal_iff
  条件: {f : α -> 实数>=0} (hf : 可测 f) {g : α -> 实数>=0∞}
  证明: aemeasurable_withDensity_ennreal_iff' hf.aemeasurable

Depends on / 依赖: aemeasurable, aemeasurable_withDensity_ennreal_iff, hf.aemeasurable
-/
theorem aemeasurable_withDensity_ennreal_iff {f : α -> Real>=0} (hf : Measurable f) {g : α -> Real>=0∞} :
    AEMeasurable g (μ.withDensity fun x => (f x : Real>=0∞)) ↔
      AEMeasurable (fun x => (f x : Real>=0∞) * g x) μ :=
aemeasurable_withDensity_ennreal_iff' hf.aemeasurable

/--
theorem `dirac_withDensity'` / 定理 `dirac_withDensity'`

English:
theorem dirac_withDensity'
  given: {f : α -> Real>=0∞} (hf : Measurable f) (a : α)
  proof: by
  ext s hs
  classical
  simp [withDensity_apply f hs, setLIntegral_dirac' hf hs, dirac_apply' _ hs,
    Set.indicator]

中文:
定理 dirac_withDensity'
  条件: {f : α -> 实数>=0∞} (hf : 可测 f) (a : α)
  证明: by
  ext s hs
  classical
  simp [withDensity_apply f hs, setLIntegral_dirac' hf hs, dirac_apply' _ hs,
    Set.indicator]

Depends on / 依赖: Set.indicator, classical, dirac_apply, indicator, setLIntegral_dirac, withDensity_apply
-/
theorem dirac_withDensity' {f : α -> Real>=0∞} (hf : Measurable f) (a : α) :
    (dirac a).withDensity f = f a • dirac a := by
  ext s hs
  classical
  simp [withDensity_apply f hs, setLIntegral_dirac' hf hs, dirac_apply' _ hs,
    Set.indicator]

/--
theorem `dirac_withDensity` / 定理 `dirac_withDensity`

English:
theorem dirac_withDensity
  given: [MeasurableSingletonClass α] (f : α -> Real>=0∞) (a : α)
  proof: by
  ext s hs
  classical
  simp [withDensity_apply f hs, setLIntegral_dirac, Set.indicator]

中文:
定理 dirac_withDensity
  条件: [MeasurableSingleton类 α] (f : α -> 实数>=0∞) (a : α)
  证明: by
  ext s hs
  classical
  simp [withDensity_apply f hs, setLIntegral_dirac, Set.indicator]

Depends on / 依赖: Set.indicator, classical, indicator, setLIntegral_dirac, withDensity_apply
-/
theorem dirac_withDensity [MeasurableSingletonClass α] (f : α -> Real>=0∞) (a : α) :
    (dirac a).withDensity f = f a • dirac a := by
  ext s hs
  classical
  simp [withDensity_apply f hs, setLIntegral_dirac, Set.indicator]

/--
theorem `count_withDensity'` / 定理 `count_withDensity'`

English:
theorem count_withDensity'
  given: {f : α -> Real>=0∞} (hf : Measurable f)
  proof: by
  simp [count, withDensity_sum, dirac_withDensity' hf _]

中文:
定理 count_withDensity'
  条件: {f : α -> 实数>=0∞} (hf : 可测 f)
  证明: by
  simp [count, withDensity_sum, dirac_withDensity' hf _]

Depends on / 依赖: dirac_withDensity, withDensity_sum
-/
theorem count_withDensity' {f : α -> Real>=0∞} (hf : Measurable f) :
    count.withDensity f = sum (fun a => f a • dirac a) := by
  simp [count, withDensity_sum, dirac_withDensity' hf _]

/--
theorem `count_withDensity` / 定理 `count_withDensity`

English:
theorem count_withDensity
  given: [MeasurableSingletonClass α] (f : α -> Real>=0∞)
  proof: by
  simp [count, withDensity_sum, dirac_withDensity]

@[fun_prop]

中文:
定理 count_withDensity
  条件: [MeasurableSingleton类 α] (f : α -> 实数>=0∞)
  证明: by
  simp [count, withDensity_sum, dirac_withDensity]

@[fun_prop]

Depends on / 依赖: dirac_withDensity, withDensity_sum
-/
theorem count_withDensity [MeasurableSingletonClass α] (f : α -> Real>=0∞) :
    count.withDensity f = sum (fun a => f a • dirac a) := by
  simp [count, withDensity_sum, dirac_withDensity]

@[fun_prop]
/--
theorem `measurable_withDensity` / 定理 `measurable_withDensity`

English:
theorem measurable_withDensity
  statement: {β : Type*} [MeasurableSpace β] {f : β -> α -> Real>=0∞}
  proof: by
  rw [Measure.measurable_measure]
  intro s hs
  simp only [withDensity_apply _ hs]
  fun_prop

中文:
定理 measurable_withDensity
  结论: {β : 类型} [可测空间 β] {f : β -> α -> 实数>=0∞}
  证明: by
  rw [Measure.measurable_measure]
  intro s hs
  simp only [withDensity_apply _ hs]
  fun_prop

Depends on / 依赖: Measure, Measure.measurable_measure, fun_prop, measurable_measure, withDensity_apply
-/
theorem measurable_withDensity {β : Type*} [MeasurableSpace β] {f : β -> α -> Real>=0∞}
    [SFinite μ] (hf : Measurable f.uncurry) :
    Measurable fun b => μ.withDensity (f b) := by
  rw [Measure.measurable_measure]
  intro s hs
  simp only [withDensity_apply _ hs]
  fun_prop

open MeasureTheory.SimpleFunc

/--
theorem `lintegral_withDensity_eq_lintegral_mul` / 定理 `lintegral_withDensity_eq_lintegral_mul`

English:
theorem lintegral_withDensity_eq_lintegral_mul
  statement: (μ : Measure α) {f : α -> Real>=0∞}
  proof: by
  apply Measurable.ennreal_induction
  · intro c s h_ms
    simp [*, mul_comm _ c, ← indicator_mul_right]
  · intro g h _ h_mea_g _ h_ind_g h_ind_h
    simp [mul_add, *, Measurable.fun_mul]
  · intro g h_mea_g h_mono_g h_ind
    have : Monotone fun n a => f a * g n a := fun m n hmn x => by dsimp; grw [h_mono_g hmn x]
    simp [lintegral_iSup, ENNReal.mul_iSup, h_mf.fun_mul (h_mea_g _), *]

中文:
定理 lintegral_withDensity_eq_lintegral_mul
  结论: (μ : 测度 α) {f : α -> 实数>=0∞}
  证明: by
  apply Measurable.ennreal_induction
  · intro c s h_ms
    simp [*, mul_comm _ c, ← indicator_mul_right]
  · intro g h _ h_mea_g _ h_ind_g h_ind_h
    simp [mul_add, *, Measurable.fun_mul]
  · intro g h_mea_g h_mono_g h_ind
    have : Monotone fun n a => f a * g n a := fun m n hmn x => by dsimp; grw [h_mono_g hmn x]
    simp [lintegral_iSup, ENNReal.mul_iSup, h_mf.fun_mul (h_mea_g _), *]

Depends on / 依赖: ENNReal, ENNReal.mul_iSup, Measurable, Measurable.ennreal_induction, Measurable.fun_mul, Monotone, ennreal_induction, fun_mul, h_ind, h_ind_g, h_ind_h, h_mea_g, h_mf, h_mf.fun_mul, h_mono_g, h_ms, indicator_mul_right, lintegral_iSup, mul_add, mul_comm
-/
theorem lintegral_withDensity_eq_lintegral_mul (μ : Measure α) {f : α -> Real>=0∞}
    (h_mf : Measurable f) :
    forall {g : α -> Real>=0∞}, Measurable g -> ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  apply Measurable.ennreal_induction
  · intro c s h_ms
    simp [*, mul_comm _ c, ← indicator_mul_right]
  · intro g h _ h_mea_g _ h_ind_g h_ind_h
    simp [mul_add, *, Measurable.fun_mul]
  · intro g h_mea_g h_mono_g h_ind
    have : Monotone fun n a => f a * g n a := fun m n hmn x => by dsimp; grw [h_mono_g hmn x]
    simp [lintegral_iSup, ENNReal.mul_iSup, h_mf.fun_mul (h_mea_g _), *]

/--
theorem `setLIntegral_withDensity_eq_setLIntegral_mul` / 定理 `setLIntegral_withDensity_eq_setLIntegral_mul`

English:
theorem setLIntegral_withDensity_eq_setLIntegral_mul
  statement: (μ : Measure α) {f g : α -> Real>=0∞}
  proof: by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]

中文:
定理 setL整数egral_withDensity_eq_setL整数egral_mul
  结论: (μ : 测度 α) {f g : α -> 实数>=0∞}
  证明: by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]

Depends on / 依赖: lintegral_withDensity_eq_lintegral_mul, restrict_withDensity
-/
theorem setLIntegral_withDensity_eq_setLIntegral_mul (μ : Measure α) {f g : α -> Real>=0∞}
    (hf : Measurable f) (hg : Measurable g) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂μ.withDensity f = ∫⁻ x in s, (f * g) x ∂μ := by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]

/--
theorem `lintegral_withDensity_eq_lintegral_mul₀'` / 定理 `lintegral_withDensity_eq_lintegral_mul₀'`

English:
theorem lintegral_withDensity_eq_lintegral_mul₀'
  statement: {μ : Measure α} {f : α -> Real>=0∞}
  proof: by
  let f' := hf.mk f
  have : μ.withDensity f = μ.withDensity f' := withDensity_congr_ae hf.ae_eq_mk
  rw [this] at hg ⊢
  let g' := hg.mk g
  calc
    ∫⁻ a, g a ∂μ.withDensity f' = ∫⁻ a, g' a ∂μ.withDensity f' := lintegral_congr_ae hg.ae_eq_mk
    _ = ∫⁻ a, (f' * g') a ∂μ :=
      (lintegral_withDensity_eq_lintegral_mul _ hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_congr_ae
      apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x != 0 }
      · have Z := hg.ae_eq_mk
        rw [EventuallyEq]; rw [ae_withDensity_iff_ae_restrict hf.measurable_mk] at Z
        filter_upwards [Z]
        intro x hx
        simp only [g', hx, Pi.mul_apply]
      · have M : MeasurableSet { x : α | f' x != 0 }ᶜ :=
          (hf.measurable_mk (measurableSet_singleton 0).compl).compl
        filter_upwards [ae_restrict_mem M]
        intro x hx
        simp only [Classical.not_not, mem_ofPred_eq, mem_compl_iff] at hx
        simp only [hx, zero_mul, Pi.mul_apply]
    _ = ∫⁻ a : α, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [f', hx, Pi.mul_apply]

中文:
定理 lintegral_withDensity_eq_lintegral_mul₀'
  结论: {μ : 测度 α} {f : α -> 实数>=0∞}
  证明: by
  let f' := hf.mk f
  have : μ.withDensity f = μ.withDensity f' := withDensity_congr_ae hf.ae_eq_mk
  rw [this] at hg ⊢
  let g' := hg.mk g
  calc
    ∫⁻ a, g a ∂μ.withDensity f' = ∫⁻ a, g' a ∂μ.withDensity f' := lintegral_congr_ae hg.ae_eq_mk
    _ = ∫⁻ a, (f' * g') a ∂μ :=
      (lintegral_withDensity_eq_lintegral_mul _ hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_congr_ae
      apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x != 0 }
      · have Z := hg.ae_eq_mk
        rw [EventuallyEq]; rw [ae_withDensity_iff_ae_restrict hf.measurable_mk] at Z
        filter_upwards [Z]
        intro x hx
        simp only [g', hx, Pi.mul_apply]
      · have M : MeasurableSet { x : α | f' x != 0 }ᶜ :=
          (hf.measurable_mk (measurableSet_singleton 0).compl).compl
        filter_upwards [ae_restrict_mem M]
        intro x hx
        simp only [Classical.not_not, mem_ofPred_eq, mem_compl_iff] at hx
        simp only [hx, zero_mul, Pi.mul_apply]
    _ = ∫⁻ a : α, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [f', hx, Pi.mul_apply]

Depends on / 依赖: EventuallyEq, ae_eq_mk, ae_of_ae_restrict_of_ae_restrict_compl, hf.ae_eq_mk, hf.measurable_mk, hf.mk, hg.ae_eq_mk, hg.measurable_mk, hg.mk, lintegral_congr_ae, lintegral_withDensity_eq_lintegral_mul, measurable_mk, withDensity, withDensity_congr_ae
-/
theorem lintegral_withDensity_eq_lintegral_mul₀' {μ : Measure α} {f : α -> Real>=0∞}
    (hf : AEMeasurable f μ) {g : α -> Real>=0∞} (hg : AEMeasurable g (μ.withDensity f)) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  let f' := hf.mk f
  have : μ.withDensity f = μ.withDensity f' := withDensity_congr_ae hf.ae_eq_mk
  rw [this] at hg ⊢
  let g' := hg.mk g
  calc
    ∫⁻ a, g a ∂μ.withDensity f' = ∫⁻ a, g' a ∂μ.withDensity f' := lintegral_congr_ae hg.ae_eq_mk
    _ = ∫⁻ a, (f' * g') a ∂μ :=
      (lintegral_withDensity_eq_lintegral_mul _ hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_congr_ae
      apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x != 0 }
      · have Z := hg.ae_eq_mk
        rw [EventuallyEq]; rw [ae_withDensity_iff_ae_restrict hf.measurable_mk] at Z
        filter_upwards [Z]
        intro x hx
        simp only [g', hx, Pi.mul_apply]
      · have M : MeasurableSet { x : α | f' x != 0 }ᶜ :=
          (hf.measurable_mk (measurableSet_singleton 0).compl).compl
        filter_upwards [ae_restrict_mem M]
        intro x hx
        simp only [Classical.not_not, mem_ofPred_eq, mem_compl_iff] at hx
        simp only [hx, zero_mul, Pi.mul_apply]
    _ = ∫⁻ a : α, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [f', hx, Pi.mul_apply]

/--
lemma `setLIntegral_withDensity_eq_lintegral_mul₀'` / 引理 `setLIntegral_withDensity_eq_lintegral_mul₀'`

English:
lemma setLIntegral_withDensity_eq_lintegral_mul₀'
  statement: {μ : Measure α} {f : α -> Real>=0∞}
  proof: by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul₀' hf.restrict]
  rw [← restrict_withDensity hs]
  exact hg.restrict

中文:
引理 setL整数egral_withDensity_eq_lintegral_mul₀'
  结论: {μ : 测度 α} {f : α -> 实数>=0∞}
  证明: by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul₀' hf.restrict]
  rw [← restrict_withDensity hs]
  exact hg.restrict

Depends on / 依赖: hf.restrict, hg.restrict, restrict, restrict_withDensity
-/
lemma setLIntegral_withDensity_eq_lintegral_mul₀' {μ : Measure α} {f : α -> Real>=0∞}
    (hf : AEMeasurable f μ) {g : α -> Real>=0∞} (hg : AEMeasurable g (μ.withDensity f))
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul₀' hf.restrict]
  rw [← restrict_withDensity hs]
  exact hg.restrict

/--
theorem `lintegral_withDensity_eq_lintegral_mul₀` / 定理 `lintegral_withDensity_eq_lintegral_mul₀`

English:
theorem lintegral_withDensity_eq_lintegral_mul₀
  statement: {μ : Measure α} {f : α -> Real>=0∞}
  proof: lintegral_withDensity_eq_lintegral_mul₀' hf (hg.mono' (withDensity_absolutelyContinuous μ f))

中文:
定理 lintegral_withDensity_eq_lintegral_mul₀
  结论: {μ : 测度 α} {f : α -> 实数>=0∞}
  证明: lintegral_withDensity_eq_lintegral_mul₀' hf (hg.mono' (withDensity_absolutelyContinuous μ f))

Depends on / 依赖: hg.mono, withDensity_absolutelyContinuous
-/
theorem lintegral_withDensity_eq_lintegral_mul₀ {μ : Measure α} {f : α -> Real>=0∞}
    (hf : AEMeasurable f μ) {g : α -> Real>=0∞} (hg : AEMeasurable g μ) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ :=
  lintegral_withDensity_eq_lintegral_mul₀' hf (hg.mono' (withDensity_absolutelyContinuous μ f))

/--
lemma `setLIntegral_withDensity_eq_lintegral_mul₀` / 引理 `setLIntegral_withDensity_eq_lintegral_mul₀`

English:
lemma setLIntegral_withDensity_eq_lintegral_mul₀
  statement: {μ : Measure α} {f : α -> Real>=0∞}
  proof: setLIntegral_withDensity_eq_lintegral_mul₀' hf
    (hg.mono' (MeasureTheory.withDensity_absolutelyContinuous μ f)) hs

中文:
引理 setL整数egral_withDensity_eq_lintegral_mul₀
  结论: {μ : 测度 α} {f : α -> 实数>=0∞}
  证明: setLIntegral_withDensity_eq_lintegral_mul₀' hf
    (hg.mono' (MeasureTheory.withDensity_absolutelyContinuous μ f)) hs

Depends on / 依赖: MeasureTheory, MeasureTheory.withDensity_absolutelyContinuous, hg.mono, withDensity_absolutelyContinuous
-/
lemma setLIntegral_withDensity_eq_lintegral_mul₀ {μ : Measure α} {f : α -> Real>=0∞}
    (hf : AEMeasurable f μ) {g : α -> Real>=0∞} (hg : AEMeasurable g μ)
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ :=
  setLIntegral_withDensity_eq_lintegral_mul₀' hf
    (hg.mono' (MeasureTheory.withDensity_absolutelyContinuous μ f)) hs

/--
theorem `lintegral_withDensity_le_lintegral_mul` / 定理 `lintegral_withDensity_le_lintegral_mul`

English:
theorem lintegral_withDensity_le_lintegral_mul
  statement: (μ : Measure α) {f : α -> Real>=0∞}
  proof: by
  rw [← iSup_lintegral_measurable_le_eq_lintegral]; rw [← iSup_lintegral_measurable_le_eq_lintegral]
  refine iSup₂_le fun i i_meas => iSup_le fun hi => ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ f_meas i_meas]
exact le_iSup₂_of_le (f * i) (f_meas.mul i_meas) le_iSup_of_le (by grw [hi]) le_rfl

中文:
定理 lintegral_withDensity_le_lintegral_mul
  结论: (μ : 测度 α) {f : α -> 实数>=0∞}
  证明: by
  rw [← iSup_lintegral_measurable_le_eq_lintegral]; rw [← iSup_lintegral_measurable_le_eq_lintegral]
  refine iSup₂_le fun i i_meas => iSup_le fun hi => ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ f_meas i_meas]
exact le_iSup₂_of_le (f * i) (f_meas.mul i_meas) le_iSup_of_le (by grw [hi]) le_rfl

Depends on / 依赖: f_meas, f_meas.mul, iSup_le, iSup_lintegral_measurable_le_eq_lintegral, i_meas, le_iSup_of_le, le_rfl, lintegral_withDensity_eq_lintegral_mul
-/
theorem lintegral_withDensity_le_lintegral_mul (μ : Measure α) {f : α -> Real>=0∞}
    (f_meas : Measurable f) (g : α -> Real>=0∞) : (∫⁻ a, g a ∂μ.withDensity f) <= ∫⁻ a, (f * g) a ∂μ := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral]; rw [← iSup_lintegral_measurable_le_eq_lintegral]
  refine iSup₂_le fun i i_meas => iSup_le fun hi => ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ f_meas i_meas]
exact le_iSup₂_of_le (f * i) (f_meas.mul i_meas) le_iSup_of_le (by grw [hi]) le_rfl

/--
theorem `lintegral_withDensity_eq_lintegral_mul_non_measurable` / 定理 `lintegral_withDensity_eq_lintegral_mul_non_measurable`

English:
theorem lintegral_withDensity_eq_lintegral_mul_non_measurable
  statement: (μ : Measure α) {f : α -> Real>=0∞}
  proof: by
  refine le_antisymm (lintegral_withDensity_le_lintegral_mul μ f_meas g) ?_
  rw [← iSup_lintegral_measurable_le_eq_lintegral]; rw [← iSup_lintegral_measurable_le_eq_lintegral]
  refine iSup₂_le fun i i_meas => iSup_le fun hi => ?_
  have A : (fun x => (f x)⁻¹ * i x) <= g := by
    intro x
    dsimp
    rw [mul_comm]; rw [← div_eq_mul_inv]
    exact div_le_of_le_mul' (hi x)
  refine le_iSup_of_le (fun x => (f x)⁻¹ * i x) (le_iSup_of_le (f_meas.fun_inv.mul i_meas) ?_)
  refine le_iSup_of_le A ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ f_meas (f_meas.fun_inv.fun_mul i_meas)]
  apply lintegral_mono_ae
  filter_upwards [hf]
  intro x h'x
  rcases eq_or_ne (f x) 0 with (hx | hx)
  · have := hi x
    simp only [hx, zero_mul, Pi.mul_apply, nonpos_iff_eq_zero] at this
    simp [this]
  · apply le_of_eq _
    dsimp
    rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel hx h'x.ne]; rw [one_mul]

中文:
定理 lintegral_withDensity_eq_lintegral_mul_non_measurable
  结论: (μ : 测度 α) {f : α -> 实数>=0∞}
  证明: by
  refine le_antisymm (lintegral_withDensity_le_lintegral_mul μ f_meas g) ?_
  rw [← iSup_lintegral_measurable_le_eq_lintegral]; rw [← iSup_lintegral_measurable_le_eq_lintegral]
  refine iSup₂_le fun i i_meas => iSup_le fun hi => ?_
  have A : (fun x => (f x)⁻¹ * i x) <= g := by
    intro x
    dsimp
    rw [mul_comm]; rw [← div_eq_mul_inv]
    exact div_le_of_le_mul' (hi x)
  refine le_iSup_of_le (fun x => (f x)⁻¹ * i x) (le_iSup_of_le (f_meas.fun_inv.mul i_meas) ?_)
  refine le_iSup_of_le A ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ f_meas (f_meas.fun_inv.fun_mul i_meas)]
  apply lintegral_mono_ae
  filter_upwards [hf]
  intro x h'x
  rcases eq_or_ne (f x) 0 with (hx | hx)
  · have := hi x
    simp only [hx, zero_mul, Pi.mul_apply, nonpos_iff_eq_zero] at this
    simp [this]
  · apply le_of_eq _
    dsimp
    rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel hx h'x.ne]; rw [one_mul]

Depends on / 依赖: div_eq_mul_inv, div_le_of_le_mul, f_meas, f_meas.fun_inv.mul, fun_inv, iSup_le, iSup_lintegral_measurable_le_eq_lintegral, i_meas, isGLB_sInf, le_antisymm, le_iSup_of_le, lintegral_withDensity, lintegral_withDensity_le_lintegral_mul, mul_comm
-/
theorem lintegral_withDensity_eq_lintegral_mul_non_measurable (μ : Measure α) {f : α -> Real>=0∞}
    (f_meas : Measurable f) (hf : forallᵐ x ∂μ, f x < ∞) (g : α -> Real>=0∞) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  refine le_antisymm (lintegral_withDensity_le_lintegral_mul μ f_meas g) ?_
  rw [← iSup_lintegral_measurable_le_eq_lintegral]; rw [← iSup_lintegral_measurable_le_eq_lintegral]
  refine iSup₂_le fun i i_meas => iSup_le fun hi => ?_
  have A : (fun x => (f x)⁻¹ * i x) <= g := by
    intro x
    dsimp
    rw [mul_comm]; rw [← div_eq_mul_inv]
    exact div_le_of_le_mul' (hi x)
  refine le_iSup_of_le (fun x => (f x)⁻¹ * i x) (le_iSup_of_le (f_meas.fun_inv.mul i_meas) ?_)
  refine le_iSup_of_le A ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ f_meas (f_meas.fun_inv.fun_mul i_meas)]
  apply lintegral_mono_ae
  filter_upwards [hf]
  intro x h'x
  rcases eq_or_ne (f x) 0 with (hx | hx)
  · have := hi x
    simp only [hx, zero_mul, Pi.mul_apply, nonpos_iff_eq_zero] at this
    simp [this]
  · apply le_of_eq _
    dsimp
    rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel hx h'x.ne]; rw [one_mul]

/--
theorem `setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable` / 定理 `setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable`

English:
theorem setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
  statement: (μ : Measure α) {f : α -> Real>=0∞}
  proof: by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas hf]

中文:
定理 setL整数egral_withDensity_eq_setL整数egral_mul_non_measurable
  结论: (μ : 测度 α) {f : α -> 实数>=0∞}
  证明: by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas hf]

Depends on / 依赖: f_meas, lintegral_withDensity_eq_lintegral_mul_non_measurable, restrict_withDensity
-/
theorem setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable (μ : Measure α) {f : α -> Real>=0∞}
    (f_meas : Measurable f) (g : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s)
    (hf : forallᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas hf]

/--
theorem `lintegral_withDensity_eq_lintegral_mul_non_measurable₀` / 定理 `lintegral_withDensity_eq_lintegral_mul_non_measurable₀`

English:
theorem lintegral_withDensity_eq_lintegral_mul_non_measurable₀
  statement: (μ : Measure α) {f : α -> Real>=0∞}
  proof: by
  let f' := hf.mk f
  calc
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, g a ∂μ.withDensity f' := by
      rw [withDensity_congr_ae hf.ae_eq_mk]
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_withDensity_eq_lintegral_mul_non_measurable _ hf.measurable_mk
      filter_upwards [h'f, hf.ae_eq_mk]
      intro x hx h'x
      rwa [← h'x]
    _ = ∫⁻ a, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [f', hx, Pi.mul_apply]

中文:
定理 lintegral_withDensity_eq_lintegral_mul_non_measurable₀
  结论: (μ : 测度 α) {f : α -> 实数>=0∞}
  证明: by
  let f' := hf.mk f
  calc
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, g a ∂μ.withDensity f' := by
      rw [withDensity_congr_ae hf.ae_eq_mk]
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_withDensity_eq_lintegral_mul_non_measurable _ hf.measurable_mk
      filter_upwards [h'f, hf.ae_eq_mk]
      intro x hx h'x
      rwa [← h'x]
    _ = ∫⁻ a, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [f', hx, Pi.mul_apply]

Depends on / 依赖: CompleteLattice, CompleteLattice.toPartialOrder, PartialOrder, Pi.mul_apply, ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.measurable_mk, hf.mk, lintegral_congr_ae, lintegral_withDensity_eq_lintegral_mul_non_measurable, measurable_mk, mul_apply, toPartialOrder, withDensity, withDensity_congr_ae
-/
theorem lintegral_withDensity_eq_lintegral_mul_non_measurable₀ (μ : Measure α) {f : α -> Real>=0∞}
    (hf : AEMeasurable f μ) (h'f : forallᵐ x ∂μ, f x < ∞) (g : α -> Real>=0∞) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  let f' := hf.mk f
  calc
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, g a ∂μ.withDensity f' := by
      rw [withDensity_congr_ae hf.ae_eq_mk]
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_withDensity_eq_lintegral_mul_non_measurable _ hf.measurable_mk
      filter_upwards [h'f, hf.ae_eq_mk]
      intro x hx h'x
      rwa [← h'x]
    _ = ∫⁻ a, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [f', hx, Pi.mul_apply]

/--
theorem `setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀` / 定理 `setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀`

English:
theorem setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀
  statement: (μ : Measure α)
  proof: by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]

中文:
定理 setL整数egral_withDensity_eq_setL整数egral_mul_non_measurable₀
  结论: (μ : 测度 α)
  证明: by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]

Depends on / 依赖: better_inf, restrict_withDensity
-/
theorem setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ (μ : Measure α)
    {f : α -> Real>=0∞} {s : Set α} (hf : AEMeasurable f (μ.restrict s)) (g : α -> Real>=0∞)
    (hs : MeasurableSet s) (h'f : forallᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]

/--
theorem `setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀'` / 定理 `setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀'`

English:
theorem setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀'
  statement: (μ : Measure α) [SFinite μ]
  proof: by
  rw [restrict_withDensity' s]; rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]

中文:
定理 setL整数egral_withDensity_eq_setL整数egral_mul_non_measurable₀'
  结论: (μ : 测度 α) [SFinite μ]
  证明: by
  rw [restrict_withDensity' s]; rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]

Depends on / 依赖: restrict_withDensity
-/
theorem setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀' (μ : Measure α) [SFinite μ]
    {f : α -> Real>=0∞} (s : Set α) (hf : AEMeasurable f (μ.restrict s)) (g : α -> Real>=0∞)
    (h'f : forallᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity' s]; rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]

/--
theorem `withDensity_mul₀` / 定理 `withDensity_mul₀`

English:
theorem withDensity_mul₀
  statement: {μ : Measure α} {f g : α -> Real>=0∞}
  proof: by
  ext1 s hs
  rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]; rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul₀ hf.restrict hg.restrict]

中文:
定理 withDensity_mul₀
  结论: {μ : 测度 α} {f g : α -> 实数>=0∞}
  证明: by
  ext1 s hs
  rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]; rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul₀ hf.restrict hg.restrict]

Depends on / 依赖: hf.restrict, hg.restrict, restrict, restrict_withDensity, withDensity_apply
-/
theorem withDensity_mul₀ {μ : Measure α} {f g : α -> Real>=0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    μ.withDensity (f * g) = (μ.withDensity f).withDensity g := by
  ext1 s hs
  rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]; rw [restrict_withDensity hs]; rw [lintegral_withDensity_eq_lintegral_mul₀ hf.restrict hg.restrict]

/--
theorem `withDensity_mul` / 定理 `withDensity_mul`

English:
theorem withDensity_mul
  given: (μ : Measure α) {f g : α -> Real>=0∞} (hf : Measurable f) (hg : Measurable g)
  proof: withDensity_mul₀ hf.aemeasurable hg.aemeasurable

中文:
定理 withDensity_mul
  条件: (μ : 测度 α) {f g : α -> 实数>=0∞} (hf : 可测 f) (hg : 可测 g)
  证明: withDensity_mul₀ hf.aemeasurable hg.aemeasurable

Depends on / 依赖: aemeasurable, better_inf, hf.aemeasurable, hg.aemeasurable
-/
theorem withDensity_mul (μ : Measure α) {f g : α -> Real>=0∞} (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity (f * g) = (μ.withDensity f).withDensity g :=
  withDensity_mul₀ hf.aemeasurable hg.aemeasurable

/--
lemma `withDensity_inv_same_le` / 引理 `withDensity_inv_same_le`

English:
lemma withDensity_inv_same_le
  given: {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
  proof: by
  change (μ.withDensity f).withDensity (fun x => (f x)⁻¹) <= μ
  rw [← withDensity_mul₀ hf hf.fun_inv]
  suffices (f * fun x => (f x)⁻¹) <=ᵐ[μ] 1 by
    refine (withDensity_mono this).trans ?_
    rw [withDensity_one]
  filter_upwards with x
  simp

中文:
引理 withDensity_inv_same_le
  条件: {μ : 测度 α} {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ)
  证明: by
  change (μ.withDensity f).withDensity (fun x => (f x)⁻¹) <= μ
  rw [← withDensity_mul₀ hf hf.fun_inv]
  suffices (f * fun x => (f x)⁻¹) <=ᵐ[μ] 1 by
    refine (withDensity_mono this).trans ?_
    rw [withDensity_one]
  filter_upwards with x
  simp

Depends on / 依赖: filter_upwards, fun_inv, hf.fun_inv, withDensity, withDensity_mono, withDensity_one
-/
lemma withDensity_inv_same_le {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasurable f μ) :
    (μ.withDensity f).withDensity f⁻¹ <= μ := by
  change (μ.withDensity f).withDensity (fun x => (f x)⁻¹) <= μ
  rw [← withDensity_mul₀ hf hf.fun_inv]
  suffices (f * fun x => (f x)⁻¹) <=ᵐ[μ] 1 by
    refine (withDensity_mono this).trans ?_
    rw [withDensity_one]
  filter_upwards with x
  simp

/--
lemma `withDensity_inv_same₀` / 引理 `withDensity_inv_same₀`

English:
lemma withDensity_inv_same₀
  statement: {μ : Measure α} {f : α -> Real>=0∞}
  proof: by
  rw [← withDensity_mul₀ hf hf.fun_inv]
  suffices (f * fun x => (f x)⁻¹) =ᵐ[μ] 1 by
    rw [withDensity_congr_ae this]; rw [withDensity_one]
  filter_upwards [hf_ne_zero, hf_ne_top] with x hf_ne_zero hf_ne_top
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_inv_cancel hf_ne_zero hf_ne_top]; rw [Pi.one_apply]

中文:
引理 withDensity_inv_same₀
  结论: {μ : 测度 α} {f : α -> 实数>=0∞}
  证明: by
  rw [← withDensity_mul₀ hf hf.fun_inv]
  suffices (f * fun x => (f x)⁻¹) =ᵐ[μ] 1 by
    rw [withDensity_congr_ae this]; rw [withDensity_one]
  filter_upwards [hf_ne_zero, hf_ne_top] with x hf_ne_zero hf_ne_top
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_inv_cancel hf_ne_zero hf_ne_top]; rw [Pi.one_apply]

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, Pi.mul_apply, Pi.one_apply, filter_upwards, fun_inv, hf.fun_inv, hf_ne_top, hf_ne_zero, mul_apply, mul_inv_cancel, one_apply, withDensity_congr_ae, withDensity_one
-/
lemma withDensity_inv_same₀ {μ : Measure α} {f : α -> Real>=0∞}
    (hf : AEMeasurable f μ) (hf_ne_zero : forallᵐ x ∂μ, f x != 0) (hf_ne_top : forallᵐ x ∂μ, f x != ∞) :
    (μ.withDensity f).withDensity (fun x => (f x)⁻¹) = μ := by
  rw [← withDensity_mul₀ hf hf.fun_inv]
  suffices (f * fun x => (f x)⁻¹) =ᵐ[μ] 1 by
    rw [withDensity_congr_ae this]; rw [withDensity_one]
  filter_upwards [hf_ne_zero, hf_ne_top] with x hf_ne_zero hf_ne_top
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_inv_cancel hf_ne_zero hf_ne_top]; rw [Pi.one_apply]

/--
lemma `withDensity_inv_same` / 引理 `withDensity_inv_same`

English:
lemma withDensity_inv_same
  statement: {μ : Measure α} {f : α -> Real>=0∞}
  proof: withDensity_inv_same₀ hf.aemeasurable hf_ne_zero hf_ne_top

中文:
引理 withDensity_inv_same
  结论: {μ : 测度 α} {f : α -> 实数>=0∞}
  证明: withDensity_inv_same₀ hf.aemeasurable hf_ne_zero hf_ne_top

Depends on / 依赖: aemeasurable, hf.aemeasurable, hf_ne_top, hf_ne_zero
-/
lemma withDensity_inv_same {μ : Measure α} {f : α -> Real>=0∞}
    (hf : Measurable f) (hf_ne_zero : forallᵐ x ∂μ, f x != 0) (hf_ne_top : forallᵐ x ∂μ, f x != ∞) :
    (μ.withDensity f).withDensity (fun x => (f x)⁻¹) = μ :=
  withDensity_inv_same₀ hf.aemeasurable hf_ne_zero hf_ne_top

/--
lemma `withDensity_absolutelyContinuous'` / 引理 `withDensity_absolutelyContinuous'`

English:
lemma withDensity_absolutelyContinuous'
  statement: {μ : Measure α} {f : α -> Real>=0∞}
  proof: by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hμs => ?_)
  rw [withDensity_apply _ hs]; rw [lintegral_eq_zero_iff' hf.restrict]; rw [ae_eq_restrict_iff_indicator_ae_eq hs]; rw [Set.indicator_zero']; rw [Filter.EventuallyEq]; rw [ae_iff] at hμs
  simp only [ae_iff, ne_eq, not_not] at hf_ne_zero
  simp only [Pi.zero_apply, Set.indicator_apply_eq_zero, not_forall, exists_prop] at hμs
  have hle : s subseteq {a | a in s ∧ ¬f a = 0} union {a | f a = 0} :=
fun x hx => or_iff_not_imp_right.mpr fun hnx => ⟨hx, hnx⟩
exact measure_mono_null hle nonpos_iff_eq_zero.1 le_trans (measure_union_le _ _)
 .symm ▸ hf_ne_zero.le hμs.symm ▸ zero_add _

中文:
引理 withDensity_absolutelyContinuous'
  结论: {μ : 测度 α} {f : α -> 实数>=0∞}
  证明: by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hμs => ?_)
  rw [withDensity_apply _ hs]; rw [lintegral_eq_zero_iff' hf.restrict]; rw [ae_eq_restrict_iff_indicator_ae_eq hs]; rw [Set.indicator_zero']; rw [Filter.EventuallyEq]; rw [ae_iff] at hμs
  simp only [ae_iff, ne_eq, not_not] at hf_ne_zero
  simp only [Pi.zero_apply, Set.indicator_apply_eq_zero, not_forall, exists_prop] at hμs
  have hle : s subseteq {a | a in s ∧ ¬f a = 0} union {a | f a = 0} :=
fun x hx => or_iff_not_imp_right.mpr fun hnx => ⟨hx, hnx⟩
exact measure_mono_null hle nonpos_iff_eq_zero.1 le_trans (measure_union_le _ _)
 .symm ▸ hf_ne_zero.le hμs.symm ▸ zero_add _

Depends on / 依赖: AbsolutelyContinuous, EventuallyEq, Filter, Filter.EventuallyEq, Measure, Measure.AbsolutelyContinuous.mk, Pi.zero_apply, Set.indicator_apply_eq_zero, Set.indicator_zero, ae_eq_restrict_iff_indicator_ae_eq, ae_iff, exists_prop, hf.restrict, hf_ne_zero, indicator_apply_eq_zero, indicator_zero, lintegral_eq_zero_iff, ne_eq, not_forall, not_not
-/
lemma withDensity_absolutelyContinuous' {μ : Measure α} {f : α -> Real>=0∞}
    (hf : AEMeasurable f μ) (hf_ne_zero : forallᵐ x ∂μ, f x != 0) :
    μ ≪ μ.withDensity f := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hμs => ?_)
  rw [withDensity_apply _ hs]; rw [lintegral_eq_zero_iff' hf.restrict]; rw [ae_eq_restrict_iff_indicator_ae_eq hs]; rw [Set.indicator_zero']; rw [Filter.EventuallyEq]; rw [ae_iff] at hμs
  simp only [ae_iff, ne_eq, not_not] at hf_ne_zero
  simp only [Pi.zero_apply, Set.indicator_apply_eq_zero, not_forall, exists_prop] at hμs
  have hle : s subseteq {a | a in s ∧ ¬f a = 0} union {a | f a = 0} :=
fun x hx => or_iff_not_imp_right.mpr fun hnx => ⟨hx, hnx⟩
exact measure_mono_null hle nonpos_iff_eq_zero.1 le_trans (measure_union_le _ _)
 .symm ▸ hf_ne_zero.le hμs.symm ▸ zero_add _

/--
theorem `withDensity_ae_eq` / 定理 `withDensity_ae_eq`

English:
theorem withDensity_ae_eq
  statement: {β : Type*} {f g : α -> β} {d : α -> Real>=0∞}
  proof: Iff.intro
  (fun h => Measure.AbsolutelyContinuous.ae_eq
    (withDensity_absolutelyContinuous' hd h_ae_nonneg) h)
  (fun h => Measure.AbsolutelyContinuous.ae_eq
    (withDensity_absolutelyContinuous μ d) h)

中文:
定理 withDensity_ae_eq
  结论: {β : 类型} {f g : α -> β} {d : α -> 实数>=0∞}
  证明: Iff.intro
  (fun h => Measure.AbsolutelyContinuous.ae_eq
    (withDensity_absolutelyContinuous' hd h_ae_nonneg) h)
  (fun h => Measure.AbsolutelyContinuous.ae_eq
    (withDensity_absolutelyContinuous μ d) h)

Depends on / 依赖: AbsolutelyContinuous, Iff.intro, Measure, Measure.AbsolutelyContinuous.ae_eq, ae_eq, h_ae_nonneg, withDensity_absolutelyContinuous
-/
theorem withDensity_ae_eq {β : Type*} {f g : α -> β} {d : α -> Real>=0∞}
    (hd : AEMeasurable d μ) (h_ae_nonneg : forallᵐ x ∂μ, d x != 0) :
    f =ᵐ[μ.withDensity d] g ↔ f =ᵐ[μ] g :=
  Iff.intro
  (fun h => Measure.AbsolutelyContinuous.ae_eq
    (withDensity_absolutelyContinuous' hd h_ae_nonneg) h)
  (fun h => Measure.AbsolutelyContinuous.ae_eq
    (withDensity_absolutelyContinuous μ d) h)

/--
Instance `SigmaFinite.withDensity` / 实例 `SigmaFinite.withDensity`

English:
instance SigmaFinite.withDensity
  signature: [SigmaFinite μ] (f : α -> Real>=0)
  body: by
  refine ⟨⟨⟨fun n => spanningSets μ n inter f ⁻¹' (Iic n), fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [withDensity_apply']
    apply setLIntegral_lt_top_of_bddAbove
    · exact ((measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ n)).ne
    · exact ⟨n, forall_mem_image.2 fun x hx => hx.2⟩
  · rw [iUnion_eq_univ_iff]
    refine fun x => ⟨max (spanningSetsIndex μ x) ⌈f x⌉₊, ?_, ?_⟩
    · exact mem_spanningSets_of_index_le _ _ (le_max_left ..)
    · simp [Nat.le_ceil]

中文:
实例 σ有限.withDensity
  签名: [σ有限 μ] (f : α -> 实数>=0)
  定义体: by
  refine ⟨⟨⟨fun n => spanningSets μ n inter f ⁻¹' (Iic n), fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [withDensity_apply']
    apply setLIntegral_lt_top_of_bddAbove
    · exact ((measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ n)).ne
    · exact ⟨n, forall_mem_image.2 fun x hx => hx.2⟩
  · rw [iUnion_eq_univ_iff]
    refine fun x => ⟨max (spanningSetsIndex μ x) ⌈f x⌉₊, ?_, ?_⟩
    · exact mem_spanningSets_of_index_le _ _ (le_max_left ..)
    · simp [Nat.le_ceil]
-/
protected instance SigmaFinite.withDensity [SigmaFinite μ] (f : α -> Real>=0) :
    SigmaFinite (μ.withDensity (fun x => f x)) := by
  refine ⟨⟨⟨fun n => spanningSets μ n inter f ⁻¹' (Iic n), fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [withDensity_apply']
    apply setLIntegral_lt_top_of_bddAbove
    · exact ((measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ n)).ne
    · exact ⟨n, forall_mem_image.2 fun x hx => hx.2⟩
  · rw [iUnion_eq_univ_iff]
    refine fun x => ⟨max (spanningSetsIndex μ x) ⌈f x⌉₊, ?_, ?_⟩
    · exact mem_spanningSets_of_index_le _ _ (le_max_left ..)
    · simp [Nat.le_ceil]

/--
lemma `SigmaFinite.withDensity_of_ne_top` / 引理 `SigmaFinite.withDensity_of_ne_top`

English:
lemma SigmaFinite.withDensity_of_ne_top
  statement: [SigmaFinite μ] {f : α -> Real>=0∞}
  proof: by
  have : f =ᵐ[μ] fun x => (f x).toNNReal := hf_ne_top.mono fun x hx => (ENNReal.coe_toNNReal hx).symm
  rw [withDensity_congr_ae this]
  infer_instance

中文:
引理 σ有限.withDensity_of_ne_top
  结论: [σ有限 μ] {f : α -> 实数>=0∞}
  证明: by
  have : f =ᵐ[μ] fun x => (f x).toNNReal := hf_ne_top.mono fun x hx => (ENNReal.coe_toNNReal hx).symm
  rw [withDensity_congr_ae this]
  infer_instance

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, coe_toNNReal, hf_ne_top, hf_ne_top.mono, infer_instance, toNNReal, withDensity_congr_ae
-/
lemma SigmaFinite.withDensity_of_ne_top [SigmaFinite μ] {f : α -> Real>=0∞}
    (hf_ne_top : forallᵐ x ∂μ, f x != ∞) : SigmaFinite (μ.withDensity f) := by
  have : f =ᵐ[μ] fun x => (f x).toNNReal := hf_ne_top.mono fun x hx => (ENNReal.coe_toNNReal hx).symm
  rw [withDensity_congr_ae this]
  infer_instance

/--
lemma `SigmaFinite.withDensity_of_ne_top'` / 引理 `SigmaFinite.withDensity_of_ne_top'`

English:
lemma SigmaFinite.withDensity_of_ne_top'
  given: [SigmaFinite μ] {f : α -> Real>=0∞} (hf_ne_top : forall x, f x != ∞)
  proof: SigmaFinite.withDensity_of_ne_top ae_of_all _ hf_ne_top

中文:
引理 σ有限.withDensity_of_ne_top'
  条件: [σ有限 μ] {f : α -> 实数>=0∞} (hf_ne_top : 对任意 x, f x != ∞)
  证明: SigmaFinite.withDensity_of_ne_top ae_of_all _ hf_ne_top

Depends on / 依赖: SigmaFinite, SigmaFinite.withDensity_of_ne_top, ae_of_all, hf_ne_top, withDensity_of_ne_top
-/
lemma SigmaFinite.withDensity_of_ne_top' [SigmaFinite μ] {f : α -> Real>=0∞} (hf_ne_top : forall x, f x != ∞) :
    SigmaFinite (μ.withDensity f) :=
SigmaFinite.withDensity_of_ne_top ae_of_all _ hf_ne_top

/--
Instance `SigmaFinite.withDensity_ofReal` / 实例 `SigmaFinite.withDensity_ofReal`

English:
instance SigmaFinite.withDensity_ofReal
  signature: [SigmaFinite μ] (f : α -> Real)
  body: .withDensity _

中文:
实例 σ有限.withDensity_of实数
  签名: [σ有限 μ] (f : α -> 实数)
  定义体: .withDensity _

Depends on / 依赖: withDensity
-/
instance SigmaFinite.withDensity_ofReal [SigmaFinite μ] (f : α -> Real) :
    SigmaFinite (μ.withDensity (fun x => ENNReal.ofReal (f x))) :=
  .withDensity _

section SFinite

variable (μ) in
/--
theorem `exists_measurable_le_withDensity_eq` / 定理 `exists_measurable_le_withDensity_eq`

English:
theorem exists_measurable_le_withDensity_eq
  given: [SFinite μ] (f : α -> Real>=0∞)
  proof: by
  obtain ⟨g, hgm, hgf, hint⟩ := exists_measurable_le_forall_setLIntegral_eq μ f
  use g, hgm, hgf
  ext s hs
  simp only [hint, withDensity_apply _ hs]

中文:
定理 存在_measurable_le_withDensity_eq
  条件: [SFinite μ] (f : α -> 实数>=0∞)
  证明: by
  obtain ⟨g, hgm, hgf, hint⟩ := exists_measurable_le_forall_setLIntegral_eq μ f
  use g, hgm, hgf
  ext s hs
  simp only [hint, withDensity_apply _ hs]

Depends on / 依赖: exists_measurable_le_forall_setLIntegral_eq, withDensity_apply
-/
theorem exists_measurable_le_withDensity_eq [SFinite μ] (f : α -> Real>=0∞) :
    exists g, Measurable g ∧ g <= f ∧ μ.withDensity g = μ.withDensity f := by
  obtain ⟨g, hgm, hgf, hint⟩ := exists_measurable_le_forall_setLIntegral_eq μ f
  use g, hgm, hgf
  ext s hs
  simp only [hint, withDensity_apply _ hs]

/--
Instance `Measure.withDensity.instSFinite` / 实例 `Measure.withDensity.instSFinite`

English:
instance Measure.withDensity.instSFinite
  signature: [SFinite μ] {f : α -> Real>=0∞}
  body: by
  wlog hfm : Measurable f generalizing f
  · rcases exists_measurable_le_withDensity_eq μ f with ⟨g, hgm, -, h⟩
    exact h ▸ this hgm
  wlog hμ : IsFiniteMeasure μ generalizing μ
  · rw [← sum_sfiniteSeq μ, withDensity_sum]
    have (n : Nat) : SFinite ((sfiniteSeq μ n).withDensity f) := this inferInstance
    infer_instance
  set s := {x | f x = ∞}
  have hs : MeasurableSet s := hfm (measurableSet_singleton _)
  have key := calc
    μ.withDensity f = μ.withDensity (sᶜ.indicator f) + μ.withDensity (s.indicator f) := by
      simp (disch := measurability) [withDensity_indicator, ← restrict_withDensity]
    _ = μ.withDensity (sᶜ.indicator f) + .sum fun _ : Nat => μ.withDensity (s.indicator 1) := by
      rw [← withDensity_tsum (by measurability)]
      congr 2 with x
      rw [ENNReal.tsum_apply]
      if hx : x in s then simpa [hx, ENNReal.tsum_const_eq_top_of_ne_zero]
      else simp [hx]
  have : SigmaFinite (μ.withDensity (sᶜ.indicator f)) := by
refine SigmaFinite.withDensity_of_ne_top ae_of_all _ fun x hx => ?_
    simp [indicator_apply, ite_eq_iff, s] at hx
  have : SigmaFinite (μ.withDensity (s.indicator 1)) := by
    rw [withDensity_indicator hs]
    exact SigmaFinite.withDensity 1
  rw [key]
  infer_instance

中文:
实例 测度.withDensity.instSFinite
  签名: [SFinite μ] {f : α -> 实数>=0∞}
  定义体: by
  wlog hfm : Measurable f generalizing f
  · rcases exists_measurable_le_withDensity_eq μ f with ⟨g, hgm, -, h⟩
    exact h ▸ this hgm
  wlog hμ : IsFiniteMeasure μ generalizing μ
  · rw [← sum_sfiniteSeq μ, withDensity_sum]
    have (n : Nat) : SFinite ((sfiniteSeq μ n).withDensity f) := this inferInstance
    infer_instance
  set s := {x | f x = ∞}
  have hs : MeasurableSet s := hfm (measurableSet_singleton _)
  have key := calc
    μ.withDensity f = μ.withDensity (sᶜ.indicator f) + μ.withDensity (s.indicator f) := by
      simp (disch := measurability) [withDensity_indicator, ← restrict_withDensity]
    _ = μ.withDensity (sᶜ.indicator f) + .sum fun _ : Nat => μ.withDensity (s.indicator 1) := by
      rw [← withDensity_tsum (by measurability)]
      congr 2 with x
      rw [ENNReal.tsum_apply]
      if hx : x in s then simpa [hx, ENNReal.tsum_const_eq_top_of_ne_zero]
      else simp [hx]
  have : SigmaFinite (μ.withDensity (sᶜ.indicator f)) := by
refine SigmaFinite.withDensity_of_ne_top ae_of_all _ fun x hx => ?_
    simp [indicator_apply, ite_eq_iff, s] at hx
  have : SigmaFinite (μ.withDensity (s.indicator 1)) := by
    rw [withDensity_indicator hs]
    exact SigmaFinite.withDensity 1
  rw [key]
  infer_instance

Depends on / 依赖: IsFiniteMeasure, Measurable, MeasurableSet, SFinite, exists_measurable_le_withDensity_eq, generalizing, indicator, infer_instance, measurableSet_singleton, s.indicator, sfiniteSeq, sum_sfiniteSeq, withDensity, withDensity_sum
-/
instance Measure.withDensity.instSFinite [SFinite μ] {f : α -> Real>=0∞} :
    SFinite (μ.withDensity f) := by
  wlog hfm : Measurable f generalizing f
  · rcases exists_measurable_le_withDensity_eq μ f with ⟨g, hgm, -, h⟩
    exact h ▸ this hgm
  wlog hμ : IsFiniteMeasure μ generalizing μ
  · rw [← sum_sfiniteSeq μ, withDensity_sum]
    have (n : Nat) : SFinite ((sfiniteSeq μ n).withDensity f) := this inferInstance
    infer_instance
  set s := {x | f x = ∞}
  have hs : MeasurableSet s := hfm (measurableSet_singleton _)
  have key := calc
    μ.withDensity f = μ.withDensity (sᶜ.indicator f) + μ.withDensity (s.indicator f) := by
      simp (disch := measurability) [withDensity_indicator, ← restrict_withDensity]
    _ = μ.withDensity (sᶜ.indicator f) + .sum fun _ : Nat => μ.withDensity (s.indicator 1) := by
      rw [← withDensity_tsum (by measurability)]
      congr 2 with x
      rw [ENNReal.tsum_apply]
      if hx : x in s then simpa [hx, ENNReal.tsum_const_eq_top_of_ne_zero]
      else simp [hx]
  have : SigmaFinite (μ.withDensity (sᶜ.indicator f)) := by
refine SigmaFinite.withDensity_of_ne_top ae_of_all _ fun x hx => ?_
    simp [indicator_apply, ite_eq_iff, s] at hx
  have : SigmaFinite (μ.withDensity (s.indicator 1)) := by
    rw [withDensity_indicator hs]
    exact SigmaFinite.withDensity 1
  rw [key]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SFinite
  signature: μ] {R
  body: by
  have : c • μ = c • ((1 : Real>=0∞) • μ) := by simp
  rw [this]; rw [← smul_assoc]; rw [← withDensity_const]
  infer_instance

中文:
实例 [SFinite
  签名: μ] {R
  定义体: by
  have : c • μ = c • ((1 : Real>=0∞) • μ) := by simp
  rw [this]; rw [← smul_assoc]; rw [← withDensity_const]
  infer_instance

Depends on / 依赖: infer_instance, smul_assoc, withDensity_const
-/
instance [SFinite μ] {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) :
    SFinite (c • μ) := by
  have : c • μ = c • ((1 : Real>=0∞) • μ) := by simp
  rw [this]; rw [← smul_assoc]; rw [← withDensity_const]
  infer_instance

/--
theorem `sFinite_of_absolutelyContinuous` / 定理 `sFinite_of_absolutelyContinuous`

English:
theorem sFinite_of_absolutelyContinuous
  given: {ν : Measure α} [SFinite ν] (hμν : μ ≪ ν)
  proof: by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) measurableSet_sigmaFiniteSetWRT]; rw [restrict_compl_sigmaFiniteSetWRT hμν]
  infer_instance

中文:
定理 sFinite_of_absolutelyContinuous
  条件: {ν : 测度 α} [SFinite ν] (hμν : μ ≪ ν)
  证明: by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) measurableSet_sigmaFiniteSetWRT]; rw [restrict_compl_sigmaFiniteSetWRT hμν]
  infer_instance

Depends on / 依赖: Measure, Measure.restrict_add_restrict_compl, infer_instance, measurableSet_sigmaFiniteSetWRT, restrict_add_restrict_compl, restrict_compl_sigmaFiniteSetWRT
-/
theorem sFinite_of_absolutelyContinuous {ν : Measure α} [SFinite ν] (hμν : μ ≪ ν) :
    SFinite μ := by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) measurableSet_sigmaFiniteSetWRT]; rw [restrict_compl_sigmaFiniteSetWRT hμν]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: α] : SFinite μ
  body: by
  obtain ⟨s, h⟩ := exists_sum_smul_dirac μ
  rw [h]
  infer_instance

中文:
实例 [可数
  签名: α] : SFinite μ
  定义体: by
  obtain ⟨s, h⟩ := exists_sum_smul_dirac μ
  rw [h]
  infer_instance

Depends on / 依赖: exists_sum_smul_dirac, infer_instance
-/
instance [Countable α] : SFinite μ := by
  obtain ⟨s, h⟩ := exists_sum_smul_dirac μ
  rw [h]
  infer_instance

end SFinite

section Prod

variable {β : Type*} {mβ : MeasurableSpace β} {ν : Measure β} [SFinite ν]

/--
theorem `prod_withDensity_left₀` / 定理 `prod_withDensity_left₀`

English:
theorem prod_withDensity_left₀
  given: {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
  proof: by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_prod _ hφ.aemeasurable]; rw [lintegral_withDensity_eq_lintegral_mul₀ hf]; rw [lintegral_withDensity_eq_lintegral_mul₀ _ hφ.aemeasurable]; rw [lintegral_prod]
  · refine lintegral_congr (fun x => ?_)
    rw [Pi.mul_apply]; rw [← lintegral_const_mul'' _ (by fun_prop)]
    simp
  all_goals fun_prop (disch := intro _ hs; simp [hs])

中文:
定理 prod_withDensity_left₀
  条件: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ)
  证明: by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_prod _ hφ.aemeasurable]; rw [lintegral_withDensity_eq_lintegral_mul₀ hf]; rw [lintegral_withDensity_eq_lintegral_mul₀ _ hφ.aemeasurable]; rw [lintegral_prod]
  · refine lintegral_congr (fun x => ?_)
    rw [Pi.mul_apply]; rw [← lintegral_const_mul'' _ (by fun_prop)]
    simp
  all_goals fun_prop (disch := intro _ hs; simp [hs])

Depends on / 依赖: Pi.mul_apply, aemeasurable, all_goals, ext_of_lintegral, fun_prop, lintegral_congr, lintegral_const_mul, lintegral_prod, mul_apply
-/
theorem prod_withDensity_left₀ {f : α -> Real>=0∞} (hf : AEMeasurable f μ) :
    (μ.withDensity f).prod ν = (μ.prod ν).withDensity (fun z => f z.1) := by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_prod _ hφ.aemeasurable]; rw [lintegral_withDensity_eq_lintegral_mul₀ hf]; rw [lintegral_withDensity_eq_lintegral_mul₀ _ hφ.aemeasurable]; rw [lintegral_prod]
  · refine lintegral_congr (fun x => ?_)
    rw [Pi.mul_apply]; rw [← lintegral_const_mul'' _ (by fun_prop)]
    simp
  all_goals fun_prop (disch := intro _ hs; simp [hs])

/--
theorem `prod_withDensity_left` / 定理 `prod_withDensity_left`

English:
theorem prod_withDensity_left
  given: {f : α -> Real>=0∞} (hf : Measurable f)
  proof: prod_withDensity_left₀ hf.aemeasurable

中文:
定理 prod_withDensity_left
  条件: {f : α -> 实数>=0∞} (hf : 可测 f)
  证明: prod_withDensity_left₀ hf.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable
-/
theorem prod_withDensity_left {f : α -> Real>=0∞} (hf : Measurable f) :
    (μ.withDensity f).prod ν = (μ.prod ν).withDensity (fun z => f z.1) :=
  prod_withDensity_left₀ hf.aemeasurable

/--
theorem `prod_withDensity_right₀` / 定理 `prod_withDensity_right₀`

English:
theorem prod_withDensity_right₀
  given: {g : β -> Real>=0∞} (hg : AEMeasurable g ν)
  proof: by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_prod _ hφ.aemeasurable]; rw [lintegral_withDensity_eq_lintegral_mul₀ _ hφ.aemeasurable]; rw [lintegral_prod]
  · refine lintegral_congr (fun x => ?_)
    rw [lintegral_withDensity_eq_lintegral_mul₀ hg (by fun_prop)]
    simp
  all_goals fun_prop (disch := intro _ hs; simp [hs])

中文:
定理 prod_withDensity_right₀
  条件: {g : β -> 实数>=0∞} (hg : 几乎处处可测 g ν)
  证明: by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_prod _ hφ.aemeasurable]; rw [lintegral_withDensity_eq_lintegral_mul₀ _ hφ.aemeasurable]; rw [lintegral_prod]
  · refine lintegral_congr (fun x => ?_)
    rw [lintegral_withDensity_eq_lintegral_mul₀ hg (by fun_prop)]
    simp
  all_goals fun_prop (disch := intro _ hs; simp [hs])

Depends on / 依赖: aemeasurable, all_goals, ext_of_lintegral, fun_prop, lintegral_congr, lintegral_prod
-/
theorem prod_withDensity_right₀ {g : β -> Real>=0∞} (hg : AEMeasurable g ν) :
    μ.prod (ν.withDensity g) = (μ.prod ν).withDensity (fun z => g z.2) := by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_prod _ hφ.aemeasurable]; rw [lintegral_withDensity_eq_lintegral_mul₀ _ hφ.aemeasurable]; rw [lintegral_prod]
  · refine lintegral_congr (fun x => ?_)
    rw [lintegral_withDensity_eq_lintegral_mul₀ hg (by fun_prop)]
    simp
  all_goals fun_prop (disch := intro _ hs; simp [hs])

/--
theorem `prod_withDensity_right` / 定理 `prod_withDensity_right`

English:
theorem prod_withDensity_right
  given: {g : β -> Real>=0∞} (hg : Measurable g)
  proof: prod_withDensity_right₀ hg.aemeasurable

中文:
定理 prod_withDensity_right
  条件: {g : β -> 实数>=0∞} (hg : 可测 g)
  证明: prod_withDensity_right₀ hg.aemeasurable

Depends on / 依赖: aemeasurable, hg.aemeasurable
-/
theorem prod_withDensity_right {g : β -> Real>=0∞} (hg : Measurable g) :
    μ.prod (ν.withDensity g) = (μ.prod ν).withDensity (fun z => g z.2) :=
  prod_withDensity_right₀ hg.aemeasurable

/--
theorem `prod_withDensity₀` / 定理 `prod_withDensity₀`

English:
theorem prod_withDensity₀
  statement: {f : α -> Real>=0∞} {g : β -> Real>=0∞}
  proof: by
  rw [prod_withDensity_left₀ hf]; rw [prod_withDensity_right₀ hg]; rw [← withDensity_mul₀]; rw [mul_comm]
  · rfl
  all_goals fun_prop (disch := intro _ hs; simp [hs])

中文:
定理 prod_withDensity₀
  结论: {f : α -> 实数>=0∞} {g : β -> 实数>=0∞}
  证明: by
  rw [prod_withDensity_left₀ hf]; rw [prod_withDensity_right₀ hg]; rw [← withDensity_mul₀]; rw [mul_comm]
  · rfl
  all_goals fun_prop (disch := intro _ hs; simp [hs])

Depends on / 依赖: all_goals, fun_prop, mul_comm
-/
theorem prod_withDensity₀ {f : α -> Real>=0∞} {g : β -> Real>=0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    (μ.withDensity f).prod (ν.withDensity g) = (μ.prod ν).withDensity (fun z => f z.1 * g z.2) := by
  rw [prod_withDensity_left₀ hf]; rw [prod_withDensity_right₀ hg]; rw [← withDensity_mul₀]; rw [mul_comm]
  · rfl
  all_goals fun_prop (disch := intro _ hs; simp [hs])

/--
theorem `prod_withDensity` / 定理 `prod_withDensity`

English:
theorem prod_withDensity
  given: {f : α -> Real>=0∞} {g : β -> Real>=0∞} (hf : Measurable f) (hg : Measurable g)
  proof: prod_withDensity₀ hf.aemeasurable hg.aemeasurable

中文:
定理 prod_withDensity
  条件: {f : α -> 实数>=0∞} {g : β -> 实数>=0∞} (hf : 可测 f) (hg : 可测 g)
  证明: prod_withDensity₀ hf.aemeasurable hg.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable, hg.aemeasurable
-/
theorem prod_withDensity {f : α -> Real>=0∞} {g : β -> Real>=0∞} (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity f).prod (ν.withDensity g) = (μ.prod ν).withDensity (fun z => f z.1 * g z.2) :=
  prod_withDensity₀ hf.aemeasurable hg.aemeasurable

-- `prod_smul_left` is in the `Prod` file. This lemma is here because this is the file in which
-- we prove the instance that gives `SFinite (c • ν)`.
/--
lemma `Measure.prod_smul_right` / 引理 `Measure.prod_smul_right`

English:
lemma Measure.prod_smul_right
  given: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R)
  proof: by
  ext s hs
  have A (s : Set β) : c • ν s = (c • 1) * ν s := by simp
  simp_rw [Measure.prod_apply hs, Measure.smul_apply, Measure.prod_apply hs, A]
  rw [lintegral_const_mul]; rw [smul_one_mul]
  exact measurable_measure_prodMk_left hs

中文:
引理 测度.prod_smul_right
  条件: {R : 类型} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞] (c : R)
  证明: by
  ext s hs
  have A (s : Set β) : c • ν s = (c • 1) * ν s := by simp
  simp_rw [Measure.prod_apply hs, Measure.smul_apply, Measure.prod_apply hs, A]
  rw [lintegral_const_mul]; rw [smul_one_mul]
  exact measurable_measure_prodMk_left hs

Depends on / 依赖: Measure, Measure.prod_apply, Measure.smul_apply, lintegral_const_mul, measurable_measure_prodMk_left, prod_apply, simp_rw, smul_apply, smul_one_mul
-/
lemma Measure.prod_smul_right {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) :
    μ.prod (c • ν) = c • (μ.prod ν) := by
  ext s hs
  have A (s : Set β) : c • ν s = (c • 1) * ν s := by simp
  simp_rw [Measure.prod_apply hs, Measure.smul_apply, Measure.prod_apply hs, A]
  rw [lintegral_const_mul]; rw [smul_one_mul]
  exact measurable_measure_prodMk_left hs

end Prod

variable [TopologicalSpace α] [OpensMeasurableSpace α] [IsLocallyFiniteMeasure μ]

/--
lemma `IsLocallyFiniteMeasure.withDensity_coe` / 引理 `IsLocallyFiniteMeasure.withDensity_coe`

English:
lemma IsLocallyFiniteMeasure.withDensity_coe
  given: {f : α -> Real>=0} (hf : Continuous f)
  proof: by
  refine ⟨fun x => ?_⟩
  rcases (μ.finiteAt_nhds x).exists_mem_basis ((nhds_basis_opens' x).restrict_subset
    ((hf.tendsto x).eventually_le_const (lt_add_one _))) with ⟨U, ⟨⟨hUx, hUo⟩, hUf⟩, hμU⟩
  refine ⟨U, hUx, ?_⟩
  rw [withDensity_apply _ hUo.measurableSet]
  exact setLIntegral_lt_top_of_bddAbove hμU.ne ⟨f x + 1, forall_mem_image.2 hUf⟩

中文:
引理 是局部有限测度.withDensity_coe
  条件: {f : α -> 实数>=0} (hf : 连续 f)
  证明: by
  refine ⟨fun x => ?_⟩
  rcases (μ.finiteAt_nhds x).exists_mem_basis ((nhds_basis_opens' x).restrict_subset
    ((hf.tendsto x).eventually_le_const (lt_add_one _))) with ⟨U, ⟨⟨hUx, hUo⟩, hUf⟩, hμU⟩
  refine ⟨U, hUx, ?_⟩
  rw [withDensity_apply _ hUo.measurableSet]
  exact setLIntegral_lt_top_of_bddAbove hμU.ne ⟨f x + 1, forall_mem_image.2 hUf⟩

Depends on / 依赖: U.ne, eventually_le_const, exists_mem_basis, finiteAt_nhds, forall_mem_image, hUo.measurableSet, hf.tendsto, lt_add_one, measurableSet, nhds_basis_opens, restrict_subset, setLIntegral_lt_top_of_bddAbove, tendsto, withDensity_apply
-/
lemma IsLocallyFiniteMeasure.withDensity_coe {f : α -> Real>=0} (hf : Continuous f) :
    IsLocallyFiniteMeasure (μ.withDensity fun x => f x) := by
  refine ⟨fun x => ?_⟩
  rcases (μ.finiteAt_nhds x).exists_mem_basis ((nhds_basis_opens' x).restrict_subset
    ((hf.tendsto x).eventually_le_const (lt_add_one _))) with ⟨U, ⟨⟨hUx, hUo⟩, hUf⟩, hμU⟩
  refine ⟨U, hUx, ?_⟩
  rw [withDensity_apply _ hUo.measurableSet]
  exact setLIntegral_lt_top_of_bddAbove hμU.ne ⟨f x + 1, forall_mem_image.2 hUf⟩

/--
lemma `IsLocallyFiniteMeasure.withDensity_ofReal` / 引理 `IsLocallyFiniteMeasure.withDensity_ofReal`

English:
lemma IsLocallyFiniteMeasure.withDensity_ofReal
  given: {f : α -> Real} (hf : Continuous f)
  proof: .withDensity_coe continuous_real_toNNReal.comp hf

中文:
引理 是局部有限测度.withDensity_of实数
  条件: {f : α -> 实数} (hf : 连续 f)
  证明: .withDensity_coe continuous_real_toNNReal.comp hf

Depends on / 依赖: continuous_real_toNNReal, continuous_real_toNNReal.comp, withDensity_coe
-/
lemma IsLocallyFiniteMeasure.withDensity_ofReal {f : α -> Real} (hf : Continuous f) :
    IsLocallyFiniteMeasure (μ.withDensity fun x => .ofReal (f x)) :=
.withDensity_coe continuous_real_toNNReal.comp hf

section Conv

variable {M : Type*} [Monoid M] [MeasurableSpace M]

-- `mconv_smul_left` is in the `Convolution` file. This lemma is here because this is the file in
-- which we prove the instance that gives `SFinite (c • ν)`.
@[to_additive conv_smul_right]
/--
theorem `Measure.mconv_smul_right` / 定理 `Measure.mconv_smul_right`

English:
theorem Measure.mconv_smul_right
  given: (μ : Measure M) (ν : Measure M) [SFinite ν] (s : Real>=0∞)
  proof: by
  unfold mconv
  rw [Measure.prod_smul_right]; rw [Measure.map_smul]

中文:
定理 测度.mconv_smul_right
  条件: (μ : 测度 M) (ν : 测度 M) [SFinite ν] (s : 实数>=0∞)
  证明: by
  unfold mconv
  rw [Measure.prod_smul_right]; rw [Measure.map_smul]

Depends on / 依赖: Measure, Measure.map_smul, Measure.prod_smul_right, map_smul, prod_smul_right
-/
theorem Measure.mconv_smul_right (μ : Measure M) (ν : Measure M) [SFinite ν] (s : Real>=0∞) :
    μ ∗ₘ (s • ν) = s • (μ ∗ₘ ν) := by
  unfold mconv
  rw [Measure.prod_smul_right]; rw [Measure.map_smul]

variable {G : Type*} [Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [IsMulLeftInvariant μ]

@[to_additive]
/--
theorem `mconv_withDensity_eq_mlconvolution₀` / 定理 `mconv_withDensity_eq_mlconvolution₀`

English:
theorem mconv_withDensity_eq_mlconvolution₀
  statement: {f g : G -> Real>=0∞}
  proof: by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_mconv_eq_lintegral_prod hφ]; rw [prod_withDensity₀ hf hg]; rw [lintegral_withDensity_eq_lintegral_mul₀]; rw [lintegral_withDensity_eq_lintegral_mul₀]; rw [lintegral_prod]; rw [lintegral_congr (fun x => by apply (lintegral_mul_left_eq_self _ x⁻¹).symm)]; rw [lintegral_lintegral_swap]
  · simp only [Pi.mul_apply, mul_inv_cancel_left, mlconvolution_def]
    conv in (∫⁻ _, _ ∂μ) * φ _ => rw [(lintegral_mul_const'' _ (by fun_prop)).symm]
  all_goals first | fun_prop | dsimp; fun_prop

@[to_additive]

中文:
定理 mconv_withDensity_eq_mlconvolution₀
  结论: {f g : G -> 实数>=0∞}
  证明: by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_mconv_eq_lintegral_prod hφ]; rw [prod_withDensity₀ hf hg]; rw [lintegral_withDensity_eq_lintegral_mul₀]; rw [lintegral_withDensity_eq_lintegral_mul₀]; rw [lintegral_prod]; rw [lintegral_congr (fun x => by apply (lintegral_mul_left_eq_self _ x⁻¹).symm)]; rw [lintegral_lintegral_swap]
  · simp only [Pi.mul_apply, mul_inv_cancel_left, mlconvolution_def]
    conv in (∫⁻ _, _ ∂μ) * φ _ => rw [(lintegral_mul_const'' _ (by fun_prop)).symm]
  all_goals first | fun_prop | dsimp; fun_prop

@[to_additive]

Depends on / 依赖: Pi.mul_apply, all_goals, ext_of_lintegral, fun_prop, lintegral_congr, lintegral_lintegral_swap, lintegral_mconv_eq_lintegral_prod, lintegral_mul_const, lintegral_mul_left_eq_self, lintegral_prod, mlconvolution_def, mul_apply, mul_inv_cancel_left
-/
theorem mconv_withDensity_eq_mlconvolution₀ {f g : G -> Real>=0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    μ.withDensity f ∗ₘ μ.withDensity g = μ.withDensity (f ⋆ₘₗ[μ] g) := by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_mconv_eq_lintegral_prod hφ]; rw [prod_withDensity₀ hf hg]; rw [lintegral_withDensity_eq_lintegral_mul₀]; rw [lintegral_withDensity_eq_lintegral_mul₀]; rw [lintegral_prod]; rw [lintegral_congr (fun x => by apply (lintegral_mul_left_eq_self _ x⁻¹).symm)]; rw [lintegral_lintegral_swap]
  · simp only [Pi.mul_apply, mul_inv_cancel_left, mlconvolution_def]
    conv in (∫⁻ _, _ ∂μ) * φ _ => rw [(lintegral_mul_const'' _ (by fun_prop)).symm]
  all_goals first | fun_prop | dsimp; fun_prop

@[to_additive]
/--
theorem `mconv_withDensity_eq_mlconvolution` / 定理 `mconv_withDensity_eq_mlconvolution`

English:
theorem mconv_withDensity_eq_mlconvolution
  statement: {f g : G -> Real>=0∞}
  proof: mconv_withDensity_eq_mlconvolution₀ hf.aemeasurable hg.aemeasurable

中文:
定理 mconv_withDensity_eq_mlconvolution
  结论: {f g : G -> 实数>=0∞}
  证明: mconv_withDensity_eq_mlconvolution₀ hf.aemeasurable hg.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable, hg.aemeasurable
-/
theorem mconv_withDensity_eq_mlconvolution {f g : G -> Real>=0∞}
    (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity f ∗ₘ μ.withDensity g = μ.withDensity (f ⋆ₘₗ[μ] g) :=
  mconv_withDensity_eq_mlconvolution₀ hf.aemeasurable hg.aemeasurable

end Conv

end MeasureTheory
