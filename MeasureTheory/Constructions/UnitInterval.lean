/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The canonical measure on the unit interval

This file provides a `MeasureTheory.MeasureSpace` instance on `unitInterval`,
and shows it is a probability measure with value zero on singletons.

It also contains some basic results on the volume of various interval sets.
-/

@[expose] public section

open scoped unitInterval
open MeasureTheory Measure Set

namespace unitInterval

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MeasureSpace I
  body: Measure.Subtype.measureSpace

中文:
实例 :
  签名: MeasureSpace I
  定义体: Measure.Subtype.measureSpace

Depends on / 依赖: Measure, Measure.Subtype.measureSpace, Subtype, measureSpace
-/
noncomputable instance : MeasureSpace I := Measure.Subtype.measureSpace

/--
theorem `volume_def` / 定理 `volume_def`

English:
theorem volume_def
  statement: (volume : Measure I) = volume.comap Subtype.val
  proof: rfl

中文:
定理 volume_def
  结论: (volume : Measure I) = volume.comap Subtype.val
  证明: rfl
-/
theorem volume_def : (volume : Measure I) = volume.comap Subtype.val := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsProbabilityMeasure (volume : Measure I)
  body: by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]; rw [Real.volume_Icc]; rw [sub_zero]; rw [ENNReal.ofReal_one]

中文:
实例 :
  签名: IsProbabilityMeasure (volume : Measure I)
  定义体: by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]; rw [Real.volume_Icc]; rw [sub_zero]; rw [ENNReal.ofReal_one]

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, Measure, Measure.Subtype.volume_univ, Real.volume_Icc, Subtype, nullMeasurableSet_Icc, ofReal_one, sub_zero, volume_Icc, volume_univ
-/
instance : IsProbabilityMeasure (volume : Measure I) where
  measure_univ := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]; rw [Real.volume_Icc]; rw [sub_zero]; rw [ENNReal.ofReal_one]

/--
lemma `measurableEmbedding_coe` / 引理 `measurableEmbedding_coe`

English:
lemma measurableEmbedding_coe
  statement: MeasurableEmbedding ((↑) : I -> Real) where
  proof: Subtype.val_injective
  measurable := measurable_subtype_coe
  measurableSet_image' _ := measurableSet_Icc.subtype_image

中文:
引理 measurableEmbedding_coe
  结论: MeasurableEmbedding ((↑) : I -> 实数) where
  证明: Subtype.val_injective
  measurable := measurable_subtype_coe
  measurableSet_image' _ := measurableSet_Icc.subtype_image

Depends on / 依赖: Subtype, Subtype.val_injective, val_injective
-/
lemma measurableEmbedding_coe : MeasurableEmbedding ((↑) : I -> Real) where
  injective := Subtype.val_injective
  measurable := measurable_subtype_coe
  measurableSet_image' _ := measurableSet_Icc.subtype_image

/--
lemma `volume_apply` / 引理 `volume_apply`

English:
lemma volume_apply
  given: {s : Set I}
  statement: volume s = volume (Subtype.val '' s)
  proof: measurableEmbedding_coe.comap_apply ..

中文:
引理 volume_apply
  条件: {s : Set I}
  结论: volume s = volume (Subtype.val '' s)
  证明: measurableEmbedding_coe.comap_apply ..

Depends on / 依赖: comap_apply, measurableEmbedding_coe, measurableEmbedding_coe.comap_apply
-/
lemma volume_apply {s : Set I} : volume s = volume (Subtype.val '' s) :=
  measurableEmbedding_coe.comap_apply ..

/--
lemma `measurePreserving_coe` / 引理 `measurePreserving_coe`

English:
lemma measurePreserving_coe
  statement: MeasurePreserving ((↑) : I -> Real) volume (volume.restrict I)
  proof: measurePreserving_subtype_coe measurableSet_Icc

中文:
引理 measurePreserving_coe
  结论: MeasurePreserving ((↑) : I -> 实数) volume (volume.restrict I)
  证明: measurePreserving_subtype_coe measurableSet_Icc

Depends on / 依赖: measurableSet_Icc, measurePreserving_subtype_coe
-/
lemma measurePreserving_coe : MeasurePreserving ((↑) : I -> Real) volume (volume.restrict I) :=
  measurePreserving_subtype_coe measurableSet_Icc

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NullSingletonClass (volume : Measure I)
  body: by simp [volume_apply]

@[fun_prop]

中文:
实例 :
  签名: NullSingletonClass (volume : Measure I)
  定义体: by simp [volume_apply]

@[fun_prop]

Depends on / 依赖: volume_apply
-/
instance : NullSingletonClass (volume : Measure I) where
  measure_singleton x := by simp [volume_apply]

@[fun_prop]
/--
theorem `measurable_symm` / 定理 `measurable_symm`

English:
theorem measurable_symm
  statement: Measurable σ
  proof: continuous_symm.measurable

中文:
定理 measurable_symm
  结论: Measurable σ
  证明: continuous_symm.measurable

Depends on / 依赖: continuous_symm, continuous_symm.measurable, measurable
-/
theorem measurable_symm : Measurable σ := continuous_symm.measurable

set_option backward.isDefEq.respectTransparency.types false in
/-- `unitInterval.symm` bundled as a measurable equivalence. -/
@[simps apply]
/--
Definition of `symmMeasurableEquiv` / `symmMeasurableEquiv` 的定义

English:
definition symmMeasurableEquiv
  signature: : I ≃ᵐ I where
  body: σ
  invFun := σ
  left_inv := symm_symm
  right_inv := symm_symm

中文:
定义 symmMeasurableEquiv
  签名: : I ≃ᵐ I where
  定义体: σ
  invFun := σ
  left_inv := symm_symm
  right_inv := symm_symm
-/
def symmMeasurableEquiv : I ≃ᵐ I where
  toFun := σ
  invFun := σ
  left_inv := symm_symm
  right_inv := symm_symm

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `symm_symmMeasurableEquiv` / 引理 `symm_symmMeasurableEquiv`

English:
lemma symm_symmMeasurableEquiv
  statement: symmMeasurableEquiv.symm = symmMeasurableEquiv
  proof: rfl

中文:
引理 symm_symmMeasurableEquiv
  结论: symmMeasurableEquiv.symm = symmMeasurableEquiv
  证明: rfl
-/
lemma symm_symmMeasurableEquiv : symmMeasurableEquiv.symm = symmMeasurableEquiv := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `coe_symmMeasurableEquiv` / 引理 `coe_symmMeasurableEquiv`

English:
lemma coe_symmMeasurableEquiv
  statement: symmMeasurableEquiv = σ
  proof: rfl

中文:
引理 coe_symmMeasurableEquiv
  结论: symmMeasurableEquiv = σ
  证明: rfl
-/
lemma coe_symmMeasurableEquiv : symmMeasurableEquiv = σ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `measurePreserving_symm` / 引理 `measurePreserving_symm`

English:
lemma measurePreserving_symm
  statement: MeasurePreserving symm volume volume where
  proof: measurable_symm
  map_eq := by
    ext s hs
.trans apply symmMeasurableEquiv.map_apply _
    conv_lhs => rw [coe_symmMeasurableEquiv, volume_apply, image_coe_preimage_symm,
      ← map_apply (by fun_prop) (measurableSet_Icc.subtype_image hs),
.map_eq, ← volume_apply] volume.measurePreserving_sub_lef

中文:
引理 measurePreserving_symm
  结论: MeasurePreserving symm volume volume where
  证明: measurable_symm
  map_eq := by
    ext s hs
.trans apply symmMeasurableEquiv.map_apply _
    conv_lhs => rw [coe_symmMeasurableEquiv, volume_apply, image_coe_preimage_symm,
      ← map_apply (by fun_prop) (measurableSet_Icc.subtype_image hs),
.map_eq, ← volume_apply] volume.measurePreserving_sub_lef

Depends on / 依赖: measurable_symm
-/
lemma measurePreserving_symm : MeasurePreserving symm volume volume where
  measurable := measurable_symm
  map_eq := by
    ext s hs
.trans apply symmMeasurableEquiv.map_apply _
    conv_lhs => rw [coe_symmMeasurableEquiv, volume_apply, image_coe_preimage_symm,
      ← map_apply (by fun_prop) (measurableSet_Icc.subtype_image hs),
.map_eq, ← volume_apply] volume.measurePreserving_sub_left 1

open Set

variable (x : I)

@[simp]
/--
lemma `volume_Iic` / 引理 `volume_Iic`

English:
lemma volume_Iic
  statement: volume (Iic x) = .ofReal x
  proof: by
  simp only [volume_apply, image_subtype_val_Icc_Iic, Real.volume_Icc, sub_zero]

@[simp]

中文:
引理 volume_Iic
  结论: volume (Iic x) = .of实数 x
  证明: by
  simp only [volume_apply, image_subtype_val_Icc_Iic, Real.volume_Icc, sub_zero]

@[simp]

Depends on / 依赖: Real.volume_Icc, image_subtype_val_Icc_Iic, sub_zero, volume_Icc, volume_apply
-/
lemma volume_Iic : volume (Iic x) = .ofReal x := by
  simp only [volume_apply, image_subtype_val_Icc_Iic, Real.volume_Icc, sub_zero]

@[simp]
/--
lemma `volume_Iio` / 引理 `volume_Iio`

English:
lemma volume_Iio
  statement: volume (Iio x) = .ofReal x
  proof: by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Iio,
    Real.volume_Ico, sub_zero]

@[simp]

中文:
引理 volume_Iio
  结论: volume (Iio x) = .of实数 x
  证明: by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Iio,
    Real.volume_Ico, sub_zero]

@[simp]

Depends on / 依赖: Real.volume_Ico, image_subtype_val_Icc_Iio, measurableSet_Icc, sub_zero, volume_Ico, volume_image_subtype_coe
-/
lemma volume_Iio : volume (Iio x) = .ofReal x := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Iio,
    Real.volume_Ico, sub_zero]

@[simp]
/--
lemma `volume_Ici` / 引理 `volume_Ici`

English:
lemma volume_Ici
  statement: volume (Ici x) = .ofReal (1 - x)
  proof: by
  simp only [volume_apply, image_subtype_val_Icc_Ici, Real.volume_Icc]

@[simp]

中文:
引理 volume_Ici
  结论: volume (Ici x) = .of实数 (1 - x)
  证明: by
  simp only [volume_apply, image_subtype_val_Icc_Ici, Real.volume_Icc]

@[simp]

Depends on / 依赖: Real.volume_Icc, image_subtype_val_Icc_Ici, volume_Icc, volume_apply
-/
lemma volume_Ici : volume (Ici x) = .ofReal (1 - x) := by
  simp only [volume_apply, image_subtype_val_Icc_Ici, Real.volume_Icc]

@[simp]
/--
lemma `volume_Ioi` / 引理 `volume_Ioi`

English:
lemma volume_Ioi
  statement: volume (Ioi x) = .ofReal (1 - x)
  proof: by
  simp only [volume_apply, image_subtype_val_Icc_Ioi, Real.volume_Ioc]

中文:
引理 volume_Ioi
  结论: volume (Ioi x) = .of实数 (1 - x)
  证明: by
  simp only [volume_apply, image_subtype_val_Icc_Ioi, Real.volume_Ioc]

Depends on / 依赖: Real.volume_Ioc, image_subtype_val_Icc_Ioi, volume_Ioc, volume_apply
-/
lemma volume_Ioi : volume (Ioi x) = .ofReal (1 - x) := by
  simp only [volume_apply, image_subtype_val_Icc_Ioi, Real.volume_Ioc]

variable (y : I)

@[simp]
/--
lemma `volume_Icc` / 引理 `volume_Icc`

English:
lemma volume_Icc
  statement: volume (Icc x y) = .ofReal (y - x)
  proof: by
  simp only [volume_apply, image_subtype_val_Icc, Real.volume_Icc]

@[simp]

中文:
引理 volume_Icc
  结论: volume (Icc x y) = .of实数 (y - x)
  证明: by
  simp only [volume_apply, image_subtype_val_Icc, Real.volume_Icc]

@[simp]

Depends on / 依赖: Real.volume_Icc, image_subtype_val_Icc, volume_Icc, volume_apply
-/
lemma volume_Icc : volume (Icc x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Icc, Real.volume_Icc]

@[simp]
/--
lemma `volume_uIcc` / 引理 `volume_uIcc`

English:
lemma volume_uIcc
  statement: volume (uIcc x y) = edist y x
  proof: by
  simp only [uIcc, volume_apply, image_subtype_val_Icc, Icc.coe_inf, Icc.coe_sup, Real.volume_Icc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

@[simp]

中文:
引理 volume_uIcc
  结论: volume (uIcc x y) = edist y x
  证明: by
  simp only [uIcc, volume_apply, image_subtype_val_Icc, Icc.coe_inf, Icc.coe_sup, Real.volume_Icc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

@[simp]

Depends on / 依赖: Icc.coe_inf, Icc.coe_sup, Real.dist_eq, Real.volume_Icc, Subtype, Subtype.dist_eq, coe_inf, coe_sup, dist_eq, edist_dist, image_subtype_val_Icc, max_sub_min_eq_abs, volume_Icc, volume_apply
-/
lemma volume_uIcc : volume (uIcc x y) = edist y x := by
  simp only [uIcc, volume_apply, image_subtype_val_Icc, Icc.coe_inf, Icc.coe_sup, Real.volume_Icc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

@[simp]
/--
lemma `volume_Ico` / 引理 `volume_Ico`

English:
lemma volume_Ico
  statement: volume (Ico x y) = .ofReal (y - x)
  proof: by
  simp only [volume_apply, image_subtype_val_Ico, Real.volume_Ico]

@[simp]

中文:
引理 volume_Ico
  结论: volume (Ico x y) = .of实数 (y - x)
  证明: by
  simp only [volume_apply, image_subtype_val_Ico, Real.volume_Ico]

@[simp]

Depends on / 依赖: Real.volume_Ico, image_subtype_val_Ico, volume_Ico, volume_apply
-/
lemma volume_Ico : volume (Ico x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Ico, Real.volume_Ico]

@[simp]
/--
lemma `volume_Ioc` / 引理 `volume_Ioc`

English:
lemma volume_Ioc
  statement: volume (Ioc x y) = .ofReal (y - x)
  proof: by
  simp only [volume_apply, image_subtype_val_Ioc, Real.volume_Ioc]

@[simp]

中文:
引理 volume_Ioc
  结论: volume (Ioc x y) = .of实数 (y - x)
  证明: by
  simp only [volume_apply, image_subtype_val_Ioc, Real.volume_Ioc]

@[simp]

Depends on / 依赖: Real.volume_Ioc, image_subtype_val_Ioc, volume_Ioc, volume_apply
-/
lemma volume_Ioc : volume (Ioc x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Ioc, Real.volume_Ioc]

@[simp]
/--
lemma `volume_uIoc` / 引理 `volume_uIoc`

English:
lemma volume_uIoc
  statement: volume (uIoc x y) = edist y x
  proof: by
  simp only [uIoc, volume_apply, image_subtype_val_Ioc, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]


@[simp]

中文:
引理 volume_uIoc
  结论: volume (uIoc x y) = edist y x
  证明: by
  simp only [uIoc, volume_apply, image_subtype_val_Ioc, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]


@[simp]

Depends on / 依赖: Icc.coe_inf, Icc.coe_sup, Real.dist_eq, Real.volume_Ioc, Subtype, Subtype.dist_eq, coe_inf, coe_sup, dist_eq, edist_dist, image_subtype_val_Ioc, max_sub_min_eq_abs, volume_Ioc, volume_apply
-/
lemma volume_uIoc : volume (uIoc x y) = edist y x := by
  simp only [uIoc, volume_apply, image_subtype_val_Ioc, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]


@[simp]
/--
lemma `volume_Ioo` / 引理 `volume_Ioo`

English:
lemma volume_Ioo
  statement: volume (Ioo x y) = .ofReal (y - x)
  proof: by
  simp only [volume_apply, image_subtype_val_Ioo, Real.volume_Ioo]

@[simp]

中文:
引理 volume_Ioo
  结论: volume (Ioo x y) = .of实数 (y - x)
  证明: by
  simp only [volume_apply, image_subtype_val_Ioo, Real.volume_Ioo]

@[simp]

Depends on / 依赖: Real.volume_Ioo, image_subtype_val_Ioo, volume_Ioo, volume_apply
-/
lemma volume_Ioo : volume (Ioo x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Ioo, Real.volume_Ioo]

@[simp]
/--
lemma `volume_uIoo` / 引理 `volume_uIoo`

English:
lemma volume_uIoo
  statement: volume (uIoo x y) = edist y x
  proof: by
  simp only [uIoo, volume_apply, image_subtype_val_Ioo, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioo,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

中文:
引理 volume_uIoo
  结论: volume (uIoo x y) = edist y x
  证明: by
  simp only [uIoo, volume_apply, image_subtype_val_Ioo, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioo,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

Depends on / 依赖: Icc.coe_inf, Icc.coe_sup, Real.dist_eq, Real.volume_Ioo, Subtype, Subtype.dist_eq, coe_inf, coe_sup, dist_eq, edist_dist, image_subtype_val_Ioo, max_sub_min_eq_abs, volume_Ioo, volume_apply
-/
lemma volume_uIoo : volume (uIoo x y) = edist y x := by
  simp only [uIoo, volume_apply, image_subtype_val_Ioo, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioo,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

end unitInterval
