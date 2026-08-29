/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Generalized polar coordinate change

Consider an `n`-dimensional normed space `E` and an additive Haar measure `μ` on `E`.
Then `μ.toSphere` is the measure on the unit sphere
such that `μ.toSphere s` equals `n • μ (Set.Ioo 0 1 • s)`.

If `n ≠ 0`, then `μ` can be represented (up to `homeomorphUnitSphereProd`)
as the product of `μ.toSphere`
and the Lebesgue measure on `(0, +∞)` taken with density `fun r ↦ r ^ n`.

One can think about this fact as a version of polar coordinate change formula
for a general nontrivial normed space.

In this file we provide a way to rewrite integrals and integrability
of functions that depend on the norm only in terms of integral over `(0, +∞)`.
We also provide a positive lower estimate on the `(Measure.toSphere μ)`-measure
of a ball of radius `ε > 0` on the unit sphere.
-/

@[expose] public section

open Set Function Metric MeasurableSpace intervalIntegral
open scoped Pointwise ENNReal NNReal

local notation "dim" => Module.finrank Real

noncomputable section
namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E]

namespace Measure

/--
Definition of `toSphere` / `toSphere` 的定义

English:
definition toSphere
  signature: (μ : Measure E)
  body: dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, mem_Ioi.2 one_pos⟩)).fst

中文:
定义 toSphere
  签名: (μ : 测度 E)
  定义体: dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, mem_Ioi.2 one_pos⟩)).fst

Depends on / 依赖: Subtype, Subtype.val, homeomorphUnitSphereProd, mem_Ioi, one_pos, restrict
-/
def toSphere (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, mem_Ioi.2 one_pos⟩)).fst

variable (μ : Measure E)

/--
theorem `toSphere_apply_aux` / 定理 `toSphere_apply_aux`

English:
theorem toSphere_apply_aux
  given: (s : Set (sphere (0 : E) 1)) (r : Ioi (0 : Real))
  proof: by
  rw [← image2_smul]; rw [image2_image_right]; rw [← Homeomorph.image_symm]; rw [image_image]; rw [← image_subtype_val_Ioi_Iio]; rw [image2_image_left]; rw [image2_swap]; rw [← image_prod]
  rfl

中文:
定理 toSphere_apply_aux
  条件: (s : 集合 (sphere (0 : E) 1)) (r : 左开右无界区间 (0 : 实数))
  证明: by
  rw [← image2_smul]; rw [image2_image_right]; rw [← Homeomorph.image_symm]; rw [image_image]; rw [← image_subtype_val_Ioi_Iio]; rw [image2_image_left]; rw [image2_swap]; rw [← image_prod]
  rfl

Depends on / 依赖: Homeomorph, Homeomorph.image_symm, image2_image_left, image2_image_right, image2_smul, image2_swap, image_image, image_prod, image_subtype_val_Ioi_Iio, image_symm
-/
theorem toSphere_apply_aux (s : Set (sphere (0 : E) 1)) (r : Ioi (0 : Real)) :
    μ ((↑) '' (homeomorphUnitSphereProd E ⁻¹' s ×ˢ Iio r)) = μ (Ioo (0 : Real) r • ((↑) '' s)) := by
  rw [← image2_smul]; rw [image2_image_right]; rw [← Homeomorph.image_symm]; rw [image_image]; rw [← image_subtype_val_Ioi_Iio]; rw [image2_image_left]; rw [image2_swap]; rw [← image_prod]
  rfl

variable [BorelSpace E]

/--
theorem `toSphere_apply'` / 定理 `toSphere_apply'`

English:
theorem toSphere_apply'
  given: {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s)
  proof: by
  rw [toSphere]; rw [smul_apply]; rw [fst_apply hs]; rw [restrict_apply (measurable_fst hs)]; rw [((MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).comp
      (Homeomorph.measurableEmbedding _)).comap_apply]; rw [image_comp]; rw [Homeomorph.image_symm]; rw [univ_prod]; rw [← Se

中文:
定理 toSphere_apply'
  条件: {s : 集合 (sphere (0 : E) 1)} (hs : 可测集 s)
  证明: by
  rw [toSphere]; rw [smul_apply]; rw [fst_apply hs]; rw [restrict_apply (measurable_fst hs)]; rw [((MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).comp
      (Homeomorph.measurableEmbedding _)).comap_apply]; rw [image_comp]; rw [Homeomorph.image_symm]; rw [univ_prod]; rw [← Se

Depends on / 依赖: Homeomorph, Homeomorph.image_symm, Homeomorph.measurableEmbedding, MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Set.prod_eq, comap_apply, fst_apply, image_comp, image_symm, measurableEmbedding, measurableSet_singleton, measurable_fst, nsmul_eq_mul, prod_eq, restrict_apply, smul_apply, subtype_coe, toSphere, toSphere_apply_aux
-/
theorem toSphere_apply' {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    μ.toSphere s = dim E * μ (Ioo (0 : Real) 1 • ((↑) '' s)) := by
  rw [toSphere]; rw [smul_apply]; rw [fst_apply hs]; rw [restrict_apply (measurable_fst hs)]; rw [((MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).comp
      (Homeomorph.measurableEmbedding _)).comap_apply]; rw [image_comp]; rw [Homeomorph.image_symm]; rw [univ_prod]; rw [← Set.prod_eq]; rw [nsmul_eq_mul]; rw [toSphere_apply_aux]

/--
theorem `toSphere_apply_univ'` / 定理 `toSphere_apply_univ'`

English:
theorem toSphere_apply_univ'
  statement: μ.toSphere univ = dim E * μ (ball 0 1 \ {0})
  proof: by
  rw [μ.toSphere_apply' .univ]; rw [image_univ]; rw [Subtype.range_coe]; rw [Ioo_smul_sphere_zero] <;> simp

中文:
定理 toSphere_apply_univ'
  结论: μ.toSphere univ = dim E * μ (ball 0 1 \ {0})
  证明: by
  rw [μ.toSphere_apply' .univ]; rw [image_univ]; rw [Subtype.range_coe]; rw [Ioo_smul_sphere_zero] <;> simp

Depends on / 依赖: Ioo_smul_sphere_zero, Subtype, Subtype.range_coe, image_univ, range_coe, toSphere_apply
-/
theorem toSphere_apply_univ' : μ.toSphere univ = dim E * μ (ball 0 1 \ {0}) := by
  rw [μ.toSphere_apply' .univ]; rw [image_univ]; rw [Subtype.range_coe]; rw [Ioo_smul_sphere_zero] <;> simp

/--
Instance `toSphere.instIsOpenPosMeasure` / 实例 `toSphere.instIsOpenPosMeasure`

English:
instance toSphere.instIsOpenPosMeasure
  signature: [FiniteDimensional Real E] [μ.IsOpenPosMeasure]
  body: by
    nontriviality E using not_nonempty_iff_eq_empty
    rintro U hUo hU
    rw [μ.toSphere_apply' hUo.measurableSet]
    apply mul_ne_zero (by simp [Module.finrank_pos.ne'])
.measure_ne_zero _ (by simpa) exact isOpen_Ioo.smul_sphere one_ne_zero (by simp) hUo

中文:
实例 toSphere.instIsOpenPosMeasure
  签名: [有限维 实数 E] [μ.是OpenPosMeasure]
  定义体: by
    nontriviality E using not_nonempty_iff_eq_empty
    rintro U hUo hU
    rw [μ.toSphere_apply' hUo.measurableSet]
    apply mul_ne_zero (by simp [Module.finrank_pos.ne'])
.measure_ne_zero _ (by simpa) exact isOpen_Ioo.smul_sphere one_ne_zero (by simp) hUo

Depends on / 依赖: Module, Module.finrank_pos.ne, finrank_pos, hUo.measurableSet, isOpen_Ioo, isOpen_Ioo.smul_sphere, measurableSet, measure_ne_zero, mul_ne_zero, nontriviality, not_nonempty_iff_eq_empty, one_ne_zero, smul_sphere, toSphere_apply
-/
instance toSphere.instIsOpenPosMeasure [FiniteDimensional Real E] [μ.IsOpenPosMeasure] :
    μ.toSphere.IsOpenPosMeasure where
  open_pos := by
    nontriviality E using not_nonempty_iff_eq_empty
    rintro U hUo hU
    rw [μ.toSphere_apply' hUo.measurableSet]
    apply mul_ne_zero (by simp [Module.finrank_pos.ne'])
.measure_ne_zero _ (by simpa) exact isOpen_Ioo.smul_sphere one_ne_zero (by simp) hUo

variable [FiniteDimensional Real E] [μ.IsAddHaarMeasure]

@[simp]
/--
theorem `toSphere_apply_univ` / 定理 `toSphere_apply_univ`

English:
theorem toSphere_apply_univ
  statement: μ.toSphere univ = dim E * μ (ball 0 1)
  proof: by
  nontriviality E
  rw [toSphere_apply_univ']; rw [measure_sdiff_null (measure_singleton _)]

@[simp]

中文:
定理 toSphere_apply_univ
  结论: μ.toSphere univ = dim E * μ (ball 0 1)
  证明: by
  nontriviality E
  rw [toSphere_apply_univ']; rw [measure_sdiff_null (measure_singleton _)]

@[simp]

Depends on / 依赖: measure_sdiff_null, measure_singleton, nontriviality, toSphere_apply_univ
-/
theorem toSphere_apply_univ : μ.toSphere univ = dim E * μ (ball 0 1) := by
  nontriviality E
  rw [toSphere_apply_univ']; rw [measure_sdiff_null (measure_singleton _)]

@[simp]
/--
theorem `toSphere_real_apply_univ` / 定理 `toSphere_real_apply_univ`

English:
theorem toSphere_real_apply_univ
  statement: μ.toSphere.real univ = dim E * μ.real (ball 0 1)
  proof: by
  simp [measureReal_def]

中文:
定理 toSphere_real_apply_univ
  结论: μ.toSphere.real univ = dim E * μ.real (ball 0 1)
  证明: by
  simp [measureReal_def]

Depends on / 依赖: measureReal_def
-/
theorem toSphere_real_apply_univ : μ.toSphere.real univ = dim E * μ.real (ball 0 1) := by
  simp [measureReal_def]

/--
theorem `toSphere_eq_zero_iff_finrank` / 定理 `toSphere_eq_zero_iff_finrank`

English:
theorem toSphere_eq_zero_iff_finrank
  statement: μ.toSphere = 0 ↔ dim E = 0
  proof: by
  rw [← measure_univ_eq_zero]; rw [toSphere_apply_univ]
  simp [IsOpen.measure_ne_zero]

中文:
定理 toSphere_eq_zero_iff_finrank
  结论: μ.toSphere = 0 ↔ dim E = 0
  证明: by
  rw [← measure_univ_eq_zero]; rw [toSphere_apply_univ]
  simp [IsOpen.measure_ne_zero]

Depends on / 依赖: IsOpen, IsOpen.measure_ne_zero, measure_ne_zero, measure_univ_eq_zero, toSphere_apply_univ
-/
theorem toSphere_eq_zero_iff_finrank : μ.toSphere = 0 ↔ dim E = 0 := by
  rw [← measure_univ_eq_zero]; rw [toSphere_apply_univ]
  simp [IsOpen.measure_ne_zero]

/--
theorem `toSphere_eq_zero_iff` / 定理 `toSphere_eq_zero_iff`

English:
theorem toSphere_eq_zero_iff
  statement: μ.toSphere = 0 ↔ Subsingleton E
  proof: μ.toSphere_eq_zero_iff_finrank.trans Module.finrank_zero_iff

@[simp]

中文:
定理 toSphere_eq_zero_iff
  结论: μ.toSphere = 0 ↔ 子单例 E
  证明: μ.toSphere_eq_zero_iff_finrank.trans Module.finrank_zero_iff

@[simp]

Depends on / 依赖: Module, Module.finrank_zero_iff, finrank_zero_iff, toSphere_eq_zero_iff_finrank, toSphere_eq_zero_iff_finrank.trans
-/
theorem toSphere_eq_zero_iff : μ.toSphere = 0 ↔ Subsingleton E :=
  μ.toSphere_eq_zero_iff_finrank.trans Module.finrank_zero_iff

@[simp]
/--
theorem `toSphere_ne_zero` / 定理 `toSphere_ne_zero`

English:
theorem toSphere_ne_zero
  given: [Nontrivial E]
  statement: μ.toSphere != 0
  proof: by
  simp [toSphere_eq_zero_iff, not_subsingleton]

中文:
定理 toSphere_ne_zero
  条件: [非平凡 E]
  结论: μ.toSphere != 0
  证明: by
  simp [toSphere_eq_zero_iff, not_subsingleton]

Depends on / 依赖: not_subsingleton, toSphere_eq_zero_iff
-/
theorem toSphere_ne_zero [Nontrivial E] : μ.toSphere != 0 := by
  simp [toSphere_eq_zero_iff, not_subsingleton]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFiniteMeasure μ.toSphere
  body: by
    rw [toSphere_apply_univ']
exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
measure_ball_lt_top.trans_le' measure_mono sdiff_subset

中文:
实例 :
  签名: 是有限测度 μ.toSphere
  定义体: by
    rw [toSphere_apply_univ']
exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
measure_ball_lt_top.trans_le' measure_mono sdiff_subset

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, ENNReal.natCast_lt_top, measure_ball_lt_top, measure_ball_lt_top.trans_le, measure_mono, mul_lt_top, natCast_lt_top, sdiff_subset, toSphere_apply_univ, trans_le
-/
instance : IsFiniteMeasure μ.toSphere where
  measure_univ_lt_top := by
    rw [toSphere_apply_univ']
exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
measure_ball_lt_top.trans_le' measure_mono sdiff_subset

/--
Definition of `volumeIoiPow` / `volumeIoiPow` 的定义

English:
definition volumeIoiPow
  signature: (n : Nat)
  body: .withDensity (.comap Subtype.val volume) fun r => .ofReal (r.1 ^ n)

中文:
定义 volumeIoiPow
  签名: (n : 自然数)
  定义体: .withDensity (.comap Subtype.val volume) fun r => .ofReal (r.1 ^ n)

Depends on / 依赖: Subtype, Subtype.val, ofReal, volume, withDensity
-/
def volumeIoiPow (n : Nat) : Measure (Ioi (0 : Real)) :=
  .withDensity (.comap Subtype.val volume) fun r => .ofReal (r.1 ^ n)

/--
lemma `volumeIoiPow_apply_Iio` / 引理 `volumeIoiPow_apply_Iio`

English:
lemma volumeIoiPow_apply_Iio
  given: (n : Nat) (x : Ioi (0 : Real))
  proof: by
  have hr₀ : 0 <= x.1 := le_of_lt x.2
  rw [volumeIoiPow]; rw [withDensity_apply _ measurableSet_Iio]; rw [setLIntegral_subtype measurableSet_Ioi _ fun a : Real => .ofReal (a ^ n)]; rw [image_subtype_val_Ioi_Iio]; rw [restrict_congr_set Ioo_ae_eq_Ioc]; rw [← ofReal_integral_eq_lintegral_ofReal (i

中文:
引理 volumeIoiPow_apply_Iio
  条件: (n : 自然数) (x : 左开右无界区间 (0 : 实数))
  证明: by
  have hr₀ : 0 <= x.1 := le_of_lt x.2
  rw [volumeIoiPow]; rw [withDensity_apply _ measurableSet_Iio]; rw [setLIntegral_subtype measurableSet_Ioi _ fun a : Real => .ofReal (a ^ n)]; rw [image_subtype_val_Ioi_Iio]; rw [restrict_congr_set Ioo_ae_eq_Ioc]; rw [← ofReal_integral_eq_lintegral_ofReal (i

Depends on / 依赖: Ioo_ae_eq_Ioc, ae_restrict_mem, filter_upwards, image_subtype_val_Ioi_Iio, integral_of_le, intervalIntegrable_pow, le_of_lt, measurableSet_Iio, measurableSet_Ioc, measurableSet_Ioi, ofReal, ofReal_integral_eq_lintegral_ofReal, pow_nonneg, restrict_congr_set, setLIntegral_subtype, volumeIoiPow, withDensity_apply
-/
lemma volumeIoiPow_apply_Iio (n : Nat) (x : Ioi (0 : Real)) :
    volumeIoiPow n (Iio x) = ENNReal.ofReal (x.1 ^ (n + 1) / (n + 1)) := by
  have hr₀ : 0 <= x.1 := le_of_lt x.2
  rw [volumeIoiPow]; rw [withDensity_apply _ measurableSet_Iio]; rw [setLIntegral_subtype measurableSet_Ioi _ fun a : Real => .ofReal (a ^ n)]; rw [image_subtype_val_Ioi_Iio]; rw [restrict_congr_set Ioo_ae_eq_Ioc]; rw [← ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow _).1]; rw [← integral_of_le hr₀]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact pow_nonneg hy.1.le _

/--
Definition of `finiteSpanningSetsIn_volumeIoiPow_range_Iio` / `finiteSpanningSetsIn_volumeIoiPow_range_Iio` 的定义

English:
definition finiteSpanningSetsIn_volumeIoiPow_range_Iio
  signature: (n : Nat)
  body: Iio ⟨k + 1, mem_Ioi.2 k.cast_add_one_pos⟩
  set_mem _ := mem_range_self _
  finite k := by simp [volumeIoiPow_apply_Iio]
  spanning := iUnion_eq_univ_iff.2 fun x => ⟨⌊x.1⌋₊, Nat.lt_floor_add_one x.1⟩

中文:
定义 finiteSpanningSetsIn_volumeIoiPow_range_Iio
  签名: (n : 自然数)
  定义体: Iio ⟨k + 1, mem_Ioi.2 k.cast_add_one_pos⟩
  set_mem _ := mem_range_self _
  finite k := by simp [volumeIoiPow_apply_Iio]
  spanning := iUnion_eq_univ_iff.2 fun x => ⟨⌊x.1⌋₊, Nat.lt_floor_add_one x.1⟩

Depends on / 依赖: cast_add_one_pos, k.cast_add_one_pos, mem_Ioi
-/
def finiteSpanningSetsIn_volumeIoiPow_range_Iio (n : Nat) :
    FiniteSpanningSetsIn (volumeIoiPow n) (range Iio) where
  set k := Iio ⟨k + 1, mem_Ioi.2 k.cast_add_one_pos⟩
  set_mem _ := mem_range_self _
  finite k := by simp [volumeIoiPow_apply_Iio]
  spanning := iUnion_eq_univ_iff.2 fun x => ⟨⌊x.1⌋₊, Nat.lt_floor_add_one x.1⟩

instance (n : Nat) : SigmaFinite (volumeIoiPow n) :=
  (finiteSpanningSetsIn_volumeIoiPow_range_Iio n).sigmaFinite

/--
theorem `measurePreserving_homeomorphUnitSphereProd` / 定理 `measurePreserving_homeomorphUnitSphereProd`

English:
theorem measurePreserving_homeomorphUnitSphereProd
  proof: by
  nontriviality E
  refine ⟨(homeomorphUnitSphereProd E).measurable, .symm ?_⟩
  refine prod_eq_generateFrom generateFrom_measurableSet
    ((borel_eq_generateFrom_Iio _).symm.trans BorelSpace.measurable_eq.symm)
    isPiSystem_measurableSet isPiSystem_Iio
    μ.toSphere.toFiniteSpanningSetsIn (f

中文:
定理 measurePreserving_homeomorphUnitSphereProd
  证明: by
  nontriviality E
  refine ⟨(homeomorphUnitSphereProd E).measurable, .symm ?_⟩
  refine prod_eq_generateFrom generateFrom_measurableSet
    ((borel_eq_generateFrom_Iio _).symm.trans BorelSpace.measurable_eq.symm)
    isPiSystem_measurableSet isPiSystem_Iio
    μ.toSphere.toFiniteSpanningSetsIn (f

Depends on / 依赖: BorelSpace, BorelSpace.measurable_eq.symm, LinearOrderedField, LinearOrderedField.smul_Ioo, Module, borel_eq_generateFrom_Iio, finiteSpanningSetsIn_volumeIoiPow_range_Iio, forall_mem_range, generateFrom_measurableSet, homeomorphUnitSphereProd, isPiSystem_Iio, isPiSystem_measurableSet, measurable, measurable_eq, nontriviality, prod_eq_generateFrom, smul_Ioo, symm.trans, toFiniteSpanningSetsIn, toSphere
-/
theorem measurePreserving_homeomorphUnitSphereProd :
    MeasurePreserving (homeomorphUnitSphereProd E) (μ.comap (↑))
      (μ.toSphere.prod (volumeIoiPow (dim E - 1))) := by
  nontriviality E
  refine ⟨(homeomorphUnitSphereProd E).measurable, .symm ?_⟩
  refine prod_eq_generateFrom generateFrom_measurableSet
    ((borel_eq_generateFrom_Iio _).symm.trans BorelSpace.measurable_eq.symm)
    isPiSystem_measurableSet isPiSystem_Iio
    μ.toSphere.toFiniteSpanningSetsIn (finiteSpanningSetsIn_volumeIoiPow_range_Iio _)
    fun s hs => forall_mem_range.2 fun r => ?_
  have : Ioo (0 : Real) r = r.1 • Ioo (0 : Real) 1 := by simp [LinearOrderedField.smul_Ioo r.2.out]
  have hpos : 0 < dim E := Module.finrank_pos
  rw [(Homeomorph.measurableEmbedding _).map_apply]; rw [toSphere_apply' _ hs]; rw [volumeIoiPow_apply_Iio]; rw [comap_subtype_coe_apply (measurableSet_singleton _).compl]; rw [toSphere_apply_aux]; rw [this]; rw [smul_assoc]; rw [μ.addHaar_smul_of_nonneg r.2.out.le]; rw [Nat.sub_add_cancel hpos]; rw [Nat.cast_pred hpos]; rw [sub_add_cancel]; rw [mul_right_comm]; rw [← ENNReal.ofReal_natCast]; rw [← ENNReal.ofReal_mul]; rw [mul_div_cancel₀]
  exacts [(Nat.cast_pos.2 hpos).ne', Nat.cast_nonneg _]

/--
lemma `ball_subset_sector_of_small_epsilon` / 引理 `ball_subset_sector_of_small_epsilon`

English:
lemma ball_subset_sector_of_small_epsilon
  proof: by
  intro y hy
  rw [mem_ball] at hy
  have habs : |1 - ε / 4| = 1 - ε / 4 := abs_of_nonneg (by linarith)
  -- Note that $y ≠ 0$.
  have hy₀ : y != 0 := by
    rintro rfl
    have : 1 - ε / 4 < ε / 4 := by simpa [norm_smul, habs, hx] using hy
    linarith
  have hy₁ : ‖y‖ < 1 := calc
    ‖y‖ <= dis

中文:
引理 ball_subset_sector_of_small_epsilon
  证明: by
  intro y hy
  rw [mem_ball] at hy
  have habs : |1 - ε / 4| = 1 - ε / 4 := abs_of_nonneg (by linarith)
  -- Note that $y ≠ 0$.
  have hy₀ : y != 0 := by
    rintro rfl
    have : 1 - ε / 4 < ε / 4 := by simpa [norm_smul, habs, hx] using hy
    linarith
  have hy₁ : ‖y‖ < 1 := calc
    ‖y‖ <= dis
-/
private lemma ball_subset_sector_of_small_epsilon
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (x : E) (hx : ‖x‖ = 1) (ε : Real) (hε : 0 < ε) (hε2 : ε <= 2) :
    ball ((1 - ε / 4) • x) (ε / 4) subseteq
      Ioo (0 : Real) 1 • (ball x ε inter sphere (0 : E) 1) := by
  intro y hy
  rw [mem_ball] at hy
  have habs : |1 - ε / 4| = 1 - ε / 4 := abs_of_nonneg (by linarith)
  -- Note that $y ≠ 0$.
  have hy₀ : y != 0 := by
    rintro rfl
    have : 1 - ε / 4 < ε / 4 := by simpa [norm_smul, habs, hx] using hy
    linarith
  have hy₁ : ‖y‖ < 1 := calc
    ‖y‖ <= dist y ((1 - ε / 4) • x) + ‖(1 - ε / 4) • x‖ := by
      simpa using dist_triangle y ((1 - ε / 4) • x) 0
    _ < ε / 4 + ‖(1 - ε / 4) • x‖ := by gcongr
    _ = 1 := by simp [norm_smul, habs, hx]
  -- Let $u = y / \|y\|$. We show $\|u - x\| < \epsilon$.
  set u : E := ‖y‖⁻¹ • y
  have hu₁ : ‖u‖ = 1 := by simp [u, hy₀, norm_smul]
  refine ⟨‖y‖, ⟨by simpa, hy₁⟩, u, ⟨?_, by simpa⟩, by simp [u, hy₀]⟩
  rw [mem_ball]
  have hyx := calc
    dist y x <= dist y ((1 - ε / 4) • x) + dist ((1 - ε / 4) • x) x := dist_triangle ..
    _ < ε / 4 + dist ((1 - ε / 4) • x) x := by gcongr
    _ = ε / 4 + ε / 4 := by simp [sub_smul, norm_smul, hx, abs_of_pos hε]
    _ = ε / 2 := by ring
  have huy : dist u y <= dist x y := by
    have H : u - y = (1 - ‖y‖) • u := by simp [u, hy₀, sub_smul]
    simpa [dist_eq_norm_sub, H, norm_smul, abs_of_nonneg, hy₁.le, hu₁, hx]
      using dist_triangle x y 0
  linarith [dist_triangle u y x, dist_comm x y]

/-- Lower estimate on the measure of the `ε`-cone in an `n`-dimensional normed space
divided by the measure of the ball. -/
@[irreducible]
/--
Definition of `toSphereBallBound` / `toSphereBallBound` 的定义

English:
definition toSphereBallBound
  signature: (n : Nat) (ε : Real)
  body: if n != 0 ∧ 0 < ε then n * ((min (Real.toNNReal ε) 2) / 4) ^ n else 1

中文:
定义 toSphereBallBound
  签名: (n : 自然数) (ε : 实数)
  定义体: if n != 0 ∧ 0 < ε then n * ((min (Real.toNNReal ε) 2) / 4) ^ n else 1

Depends on / 依赖: Real.toNNReal, toNNReal
-/
noncomputable def toSphereBallBound (n : Nat) (ε : Real) : Real>=0 :=
  if n != 0 ∧ 0 < ε then n * ((min (Real.toNNReal ε) 2) / 4) ^ n else 1

/--
theorem `toSphereBallBound_pos` / 定理 `toSphereBallBound_pos`

English:
theorem toSphereBallBound_pos
  given: (n : Nat) (ε : Real)
  statement: 0 < toSphereBallBound n ε
  proof: by
  unfold toSphereBallBound
  split_ifs with h
  · cases h
    positivity
  · positivity

中文:
定理 toSphereBallBound_pos
  条件: (n : 自然数) (ε : 实数)
  结论: 0 < toSphereBallBound n ε
  证明: by
  unfold toSphereBallBound
  split_ifs with h
  · cases h
    positivity
  · positivity

Depends on / 依赖: split_ifs, toSphereBallBound
-/
theorem toSphereBallBound_pos (n : Nat) (ε : Real) : 0 < toSphereBallBound n ε := by
  unfold toSphereBallBound
  split_ifs with h
  · cases h
    positivity
  · positivity

/--
theorem `toSphereBallBound_mul_measure_unitBall_le_toSphere_ball` / 定理 `toSphereBallBound_mul_measure_unitBall_le_toSphere_ball`

English:
theorem toSphereBallBound_mul_measure_unitBall_le_toSphere_ball
  statement: {ε : Real}
  proof: by
  have : Nontrivial E := ⟨⟨x, 0, ne_of_apply_ne Norm.norm (by simp)⟩⟩
  wlog hε₂ : ε <= 2 generalizing ε
  · trans μ.toSphere (ball x (min ε 2))
    · simpa [Real.toNNReal_monotone.map_min, toSphereBallBound]
        using this (ε := min ε 2) (by simp [hε]) (by simp)
    · gcongr
      simp
  rw 

中文:
定理 toSphereBallBound_mul_measure_unitBall_le_toSphere_ball
  结论: {ε : 实数}
  证明: by
  have : Nontrivial E := ⟨⟨x, 0, ne_of_apply_ne Norm.norm (by simp)⟩⟩
  wlog hε₂ : ε <= 2 generalizing ε
  · trans μ.toSphere (ball x (min ε 2))
    · simpa [Real.toNNReal_monotone.map_min, toSphereBallBound]
        using this (ε := min ε 2) (by simp [hε]) (by simp)
    · gcongr
      simp
  rw 

Depends on / 依赖: Module, Module.finrank, Module.finrank_pos.ne, Nontrivial, Norm.norm, Real.toNNReal_monotone.map_min, Subtype, Subtype.image_ball, ball_subset_sector_of_small_epsilon, finrank, finrank_pos, generalizing, image_ball, map_min, measurableSet_ball, ne_of_apply_ne, ofPred_mem_eq, toNNReal_monotone, toSphere, toSphereBallBound
-/
theorem toSphereBallBound_mul_measure_unitBall_le_toSphere_ball {ε : Real}
    (hε : 0 < ε) (x : sphere (0 : E) 1) :
    toSphereBallBound (Module.finrank Real E) ε * μ (ball 0 1) <= μ.toSphere (ball x ε) := by
  have : Nontrivial E := ⟨⟨x, 0, ne_of_apply_ne Norm.norm (by simp)⟩⟩
  wlog hε₂ : ε <= 2 generalizing ε
  · trans μ.toSphere (ball x (min ε 2))
    · simpa [Real.toNNReal_monotone.map_min, toSphereBallBound]
        using this (ε := min ε 2) (by simp [hε]) (by simp)
    · gcongr
      simp
  rw [μ.toSphere_apply' measurableSet_ball]; rw [Subtype.image_ball]; rw [ofPred_mem_eq]
  grw [← ball_subset_sector_of_small_epsilon] <;> try assumption
  · have hdim : Module.finrank Real E != 0 := Module.finrank_pos.ne'
    have : min (ENNReal.ofReal ε) 2 = ENNReal.ofReal ε := by simpa
    simp (disch := positivity) [μ.addHaar_ball_of_pos (r := ε / 4), ENNReal.ofReal_div_of_pos,
      toSphereBallBound, mul_assoc, ENNReal.ofNNReal_toNNReal, this, hdim, hε]
  · simp

/--
theorem `toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball` / 定理 `toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball`

English:
theorem toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
  proof: by
  grw [Measure.real, Measure.real, ← toSphereBallBound_mul_measure_unitBall_le_toSphere_ball μ hε,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp

中文:
定理 toSphereBallBound_mul_measure实数_unitBall_le_toSphere_ball
  证明: by
  grw [Measure.real, Measure.real, ← toSphereBallBound_mul_measure_unitBall_le_toSphere_ball μ hε,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp

Depends on / 依赖: ENNReal, ENNReal.coe_toReal, ENNReal.toReal_mul, Measure, Measure.real, coe_toReal, toReal_mul, toSphereBallBound_mul_measure_unitBall_le_toSphere_ball
-/
theorem toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
    {ε : Real} (hε : 0 < ε) (x : sphere (0 : E) 1) :
    toSphereBallBound (Module.finrank Real E) ε * μ.real (ball 0 1) <=
      μ.toSphere.real (ball x ε) := by
  grw [Measure.real, Measure.real, ← toSphereBallBound_mul_measure_unitBall_le_toSphere_ball μ hε,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp

end Measure

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [Nontrivial E] (μ : Measure E) [FiniteDimensional Real E] [BorelSpace E] [μ.IsAddHaarMeasure]

/--
lemma `integrable_fun_norm_addHaar` / 引理 `integrable_fun_norm_addHaar`

English:
lemma integrable_fun_norm_addHaar
  given: {f : Real -> F}
  proof: by
  have := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb (g := f ∘ (↑) ∘ Prod.snd)
    (Homeomorph.measurableEmbedding _)
  simp only [comp_def, homeomorphUnitSphereProd_apply_snd_coe] at this
  rw [← restrict_compl_singleton (μ := μ) 0]; rw [← IntegrableOn]; rw [integrableOn_if

中文:
引理 integrable_fun_norm_addHaar
  条件: {f : 实数 -> F}
  证明: by
  have := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb (g := f ∘ (↑) ∘ Prod.snd)
    (Homeomorph.measurableEmbedding _)
  simp only [comp_def, homeomorphUnitSphereProd_apply_snd_coe] at this
  rw [← restrict_compl_singleton (μ := μ) 0]; rw [← IntegrableOn]; rw [integrableOn_if

Depends on / 依赖: Homeomorph, Homeomorph.measurableEmbedding, Integrable, Integrable.comp_snd_iff, IntegrableOn, Measure, Measure.volume, Prod.snd, Subtype, Subtype.val, comp_def, comp_snd_iff, homeomorphUnitSphereProd_apply_snd_coe, integrableOn_iff_comap_subtypeVal, integrable_comp_emb, measurability, measurableEmbedding, measurePreserving_homeomorphUnitSphereProd, measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb, restrict_compl_singleton
-/
lemma integrable_fun_norm_addHaar {f : Real -> F} :
    Integrable (f ‖·‖) μ ↔ IntegrableOn (fun y : Real => y ^ (dim E - 1) • f y) (Ioi 0) := by
  have := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb (g := f ∘ (↑) ∘ Prod.snd)
    (Homeomorph.measurableEmbedding _)
  simp only [comp_def, homeomorphUnitSphereProd_apply_snd_coe] at this
  rw [← restrict_compl_singleton (μ := μ) 0]; rw [← IntegrableOn]; rw [integrableOn_iff_comap_subtypeVal (by measurability)]; rw [comp_def]; rw [this]; rw [Integrable.comp_snd_iff (β := Ioi 0) (f := (f <| Subtype.val ·))]; rw [integrableOn_iff_comap_subtypeVal]; rw [comp_def]; rw [Measure.volumeIoiPow]; rw [integrable_withDensity_iff_integrable_smul']; rw [integrable_congr]
  · refine .of_forall ?_
    rintro ⟨x, hx : 0 < x⟩
    simp (disch := positivity) [ENNReal.toReal_ofReal]
  · fun_prop
  · simp
  · measurability
  · simp

/--
lemma `integrableOn_fun_norm_addHaar` / 引理 `integrableOn_fun_norm_addHaar`

English:
lemma integrableOn_fun_norm_addHaar
  given: {f : Real -> F} {r : Real}
  proof: by
  calc
    _ ↔ Integrable (fun x => (Iio r).indicator f ‖x‖) μ := by
      rw [← integrable_indicator_iff measurableSet_ball]
      apply integrable_congr
      filter_upwards with x
      simp [indicator]
    _ ↔ IntegrableOn ((Ioo 0 r).indicator fun y => y ^ (Module.finrank Real E - 1) • f y) (

中文:
引理 integrableOn_fun_norm_addHaar
  条件: {f : 实数 -> F} {r : 实数}
  证明: by
  calc
    _ ↔ Integrable (fun x => (Iio r).indicator f ‖x‖) μ := by
      rw [← integrable_indicator_iff measurableSet_ball]
      apply integrable_congr
      filter_upwards with x
      simp [indicator]
    _ ↔ IntegrableOn ((Ioo 0 r).indicator fun y => y ^ (Module.finrank Real E - 1) • f y) (

Depends on / 依赖: Integrable, IntegrableOn, Module, Module.finrank, filter_upwards, finrank, indicator, integrableOn_congr_fun, integrable_congr, integrable_fun_norm_addHaar, integrable_indicator_iff, measurableSet_Ioi, measurableSet_ball
-/
lemma integrableOn_fun_norm_addHaar {f : Real -> F} {r : Real} :
    IntegrableOn (fun x : E => f ‖x‖) (ball (0 : E) r) μ ↔
    IntegrableOn (fun y => y ^ (Module.finrank Real E - 1) • f y) (Ioo 0 r) := by
  calc
    _ ↔ Integrable (fun x => (Iio r).indicator f ‖x‖) μ := by
      rw [← integrable_indicator_iff measurableSet_ball]
      apply integrable_congr
      filter_upwards with x
      simp [indicator]
    _ ↔ IntegrableOn ((Ioo 0 r).indicator fun y => y ^ (Module.finrank Real E - 1) • f y) (Ioi 0) := by
      rw [integrable_fun_norm_addHaar μ (f := indicator (Iio r) f)]; rw [integrableOn_congr_fun _ measurableSet_Ioi]
      intro x (hx : 0 < x)
      by_cases hxr : x < r <;> simp [hxr, hx]
    _ ↔ Integrable ((Ioo 0 r).indicator fun y => y ^ (Module.finrank Real E - 1) • f y) := by
      rw [MeasureTheory.integrableOn_iff_integrable_of_support_subset]
      intro x hx
      simp only [support_indicator, mem_inter_iff, mem_Ioo, Function.mem_support, ne_eq,
        smul_eq_zero, pow_eq_zero_iff', not_or, not_and, Decidable.not_not] at hx
      refine mem_Ioi.mpr hx.1.1
    _ ↔ IntegrableOn (fun y => y ^ (Module.finrank Real E - 1) • f y) (Ioo 0 r) volume := by
      rw [← integrable_indicator_iff measurableSet_Ioo]; rw [← integrableOn_univ]

/--
lemma `integral_fun_norm_addHaar` / 引理 `integral_fun_norm_addHaar`

English:
lemma integral_fun_norm_addHaar
  given: (f : Real -> F)
  proof: calc
    ∫ x, f (‖x‖) ∂μ = ∫ x : ({(0)}ᶜ : Set E), f (‖x.1‖) ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl fun x => f (‖x‖)]; rw [restrict_compl_singleton]
    _ = ∫ x, f x.2 ∂μ.toSphere.prod (.volumeIoiPow (dim E - 1)) := by
      simpa using μ.measurePrese

中文:
引理 integral_fun_norm_addHaar
  条件: (f : 实数 -> F)
  证明: calc
    ∫ x, f (‖x‖) ∂μ = ∫ x : ({(0)}ᶜ : Set E), f (‖x.1‖) ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl fun x => f (‖x‖)]; rw [restrict_compl_singleton]
    _ = ∫ x, f x.2 ∂μ.toSphere.prod (.volumeIoiPow (dim E - 1)) := by
      simpa using μ.measurePrese

Depends on / 依赖: Homeomorph, Homeomorph.measurableEmbedding, Prod.snd, Subtyp, Subtype, Subtype.val, integral_comp, integral_fun_snd, integral_subtype_comap, measurableEmbedding, measurableSet_singleton, measurePreserving_homeomorphUnitSphereProd, measurePreserving_homeomorphUnitSphereProd.integral_comp, restrict_compl_singleton, toSphere, toSphere.prod, toSphere.real, volumeIoiPow
-/
lemma integral_fun_norm_addHaar (f : Real -> F) :
    ∫ x, f (‖x‖) ∂μ = dim E • μ.real (ball 0 1) • ∫ y in Ioi (0 : Real), y ^ (dim E - 1) • f y :=
  calc
    ∫ x, f (‖x‖) ∂μ = ∫ x : ({(0)}ᶜ : Set E), f (‖x.1‖) ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl fun x => f (‖x‖)]; rw [restrict_compl_singleton]
    _ = ∫ x, f x.2 ∂μ.toSphere.prod (.volumeIoiPow (dim E - 1)) := by
      simpa using μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) (f ∘ Subtype.val ∘ Prod.snd)
    _ = μ.toSphere.real univ • ∫ x : Ioi (0 : Real), f x ∂.volumeIoiPow (dim E - 1) :=
      integral_fun_snd (f ∘ Subtype.val)
    _ = _ := by
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul]; rw [μ.toSphere_real_apply_univ]; rw [← nsmul_eq_mul]; rw [smul_assoc]; rw [integral_subtype_comap measurableSet_Ioi fun a => Real.toNNReal (a ^ (dim E - 1)) • f a]; rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
      · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]
      · exact (measurable_subtype_coe.pow_const _).real_toNNReal

end MeasureTheory
