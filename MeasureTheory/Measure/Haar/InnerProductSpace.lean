/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Volume forms and measures on inner product spaces

A volume form induces a Lebesgue measure on general finite-dimensional real vector spaces. In this
file, we discuss the specific situation of inner product spaces, where an orientation gives
rise to a canonical volume form. We show that the measure coming from this volume form gives
measure `1` to the parallelepiped spanned by any orthonormal basis, and that it coincides with
the canonical `volume` from the `MeasureSpace` instance.
-/

@[expose] public section

open Module MeasureTheory MeasureTheory.Measure Set WithLp

variable {ι E F : Type*}

variable [NormedAddCommGroup F] [InnerProductSpace Real F]
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

namespace LinearIsometryEquiv

variable (f : E ≃ₗᵢ[Real] F)

/--
Definition of `toMeasurableEquiv` / `toMeasurableEquiv` 的定义

English:
definition toMeasurableEquiv
  signature: : E ≃ᵐ F
  body: f.toHomeomorph.toMeasurableEquiv

中文:
定义 toMeasurableEquiv
  签名: : E ≃ᵐ F
  定义体: f.toHomeomorph.toMeasurableEquiv

Depends on / 依赖: f.toHomeomorph.toMeasurableEquiv, toHomeomorph, toMeasurableEquiv
-/
def toMeasurableEquiv : E ≃ᵐ F := f.toHomeomorph.toMeasurableEquiv

/--
theorem `coe_toMeasurableEquiv` / 定理 `coe_toMeasurableEquiv`

English:
theorem coe_toMeasurableEquiv
  statement: (f.toMeasurableEquiv : E -> F) = f
  proof: rfl

中文:
定理 coe_toMeasurableEquiv
  结论: (f.toMeasurableEquiv : E -> F) = f
  证明: rfl
-/
@[simp] theorem coe_toMeasurableEquiv : (f.toMeasurableEquiv : E -> F) = f := rfl

/--
theorem `toMeasurableEquiv_symm` / 定理 `toMeasurableEquiv_symm`

English:
theorem toMeasurableEquiv_symm
  statement: f.symm.toMeasurableEquiv = f.toMeasurableEquiv.symm
  proof: rfl

中文:
定理 toMeasurableEquiv_symm
  结论: f.symm.toMeasurableEquiv = f.toMeasurableEquiv.symm
  证明: rfl
-/
@[simp] theorem toMeasurableEquiv_symm : f.symm.toMeasurableEquiv = f.toMeasurableEquiv.symm := rfl

/--
lemma `coe_symm_toMeasurableEquiv` / 引理 `coe_symm_toMeasurableEquiv`

English:
lemma coe_symm_toMeasurableEquiv
  statement: ⇑f.toMeasurableEquiv.symm = f.symm
  proof: rfl

中文:
引理 coe_symm_toMeasurableEquiv
  结论: ⇑f.toMeasurableEquiv.symm = f.symm
  证明: rfl
-/
@[simp] lemma coe_symm_toMeasurableEquiv : ⇑f.toMeasurableEquiv.symm = f.symm := rfl

end LinearIsometryEquiv

variable [Fintype ι]
variable [FiniteDimensional Real E] [FiniteDimensional Real F]

section
variable {m n : Nat} [_i : Fact (finrank Real F = n)]

/--
theorem `Orientation.measure_orthonormalBasis` / 定理 `Orientation.measure_orthonormalBasis`

English:
theorem Orientation.measure_orthonormalBasis
  statement: (o : Orientation Real F (Fin n))
  proof: by
  have e : ι ≃ Fin n := by
    refine Fintype.equivFinOfCardEq ?_
    rw [← _i.out]; rw [finrank_eq_card_basis b.toBasis]
  have A : ⇑b = b.reindex e ∘ e := by
    ext x
    simp only [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  rw [A]; rw [parallelepiped_comp_equ

中文:
定理 定向.measure_orthonormalBasis
  结论: (o : 定向 实数 F (有限集 n))
  证明: by
  have e : ι ≃ Fin n := by
    refine Fintype.equivFinOfCardEq ?_
    rw [← _i.out]; rw [finrank_eq_card_basis b.toBasis]
  have A : ⇑b = b.reindex e ∘ e := by
    ext x
    simp only [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  rw [A]; rw [parallelepiped_comp_equ

Depends on / 依赖: AlternatingMap, AlternatingMap.measure_parallelepiped, ENNReal, ENNReal.ofReal_one, Equiv.symm_apply_apply, Fintype, Fintype.equivFinOfCardEq, Function, Function.comp_apply, OrthonormalBasis, OrthonormalBasis.coe_reindex, _i.out, abs_volumeForm_apply_of_orthonormal, b.reindex, b.toBasis, coe_reindex, comp_apply, equivFinOfCardEq, finrank_eq_card_basis, measure_parallelepiped
-/
theorem Orientation.measure_orthonormalBasis (o : Orientation Real F (Fin n))
    (b : OrthonormalBasis ι Real F) : o.volumeForm.measure (parallelepiped b) = 1 := by
  have e : ι ≃ Fin n := by
    refine Fintype.equivFinOfCardEq ?_
    rw [← _i.out]; rw [finrank_eq_card_basis b.toBasis]
  have A : ⇑b = b.reindex e ∘ e := by
    ext x
    simp only [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  rw [A]; rw [parallelepiped_comp_equiv]; rw [AlternatingMap.measure_parallelepiped]; rw [o.abs_volumeForm_apply_of_orthonormal]; rw [ENNReal.ofReal_one]

/--
theorem `Orientation.measure_eq_volume` / 定理 `Orientation.measure_eq_volume`

English:
theorem Orientation.measure_eq_volume
  given: (o : Orientation Real F (Fin n))
  proof: by
  have A : o.volumeForm.measure (stdOrthonormalBasis Real F).toBasis.parallelepiped = 1 :=
    Orientation.measure_orthonormalBasis o (stdOrthonormalBasis Real F)
  rw [addHaarMeasure_unique o.volumeForm.measure
    (stdOrthonormalBasis Real F).toBasis.parallelepiped]; rw [A]; rw [one_smul]
  sim

中文:
定理 定向.measure_eq_volume
  条件: (o : 定向 实数 F (有限集 n))
  证明: by
  have A : o.volumeForm.measure (stdOrthonormalBasis Real F).toBasis.parallelepiped = 1 :=
    Orientation.measure_orthonormalBasis o (stdOrthonormalBasis Real F)
  rw [addHaarMeasure_unique o.volumeForm.measure
    (stdOrthonormalBasis Real F).toBasis.parallelepiped]; rw [A]; rw [one_smul]
  sim

Depends on / 依赖: Basis.addHaar, Orientation, Orientation.measure_orthonormalBasis, addHaar, addHaarMeasure_unique, measure, measure_orthonormalBasis, o.volumeForm.measure, one_smul, parallelepiped, stdOrthonormalBasis, toBasis, toBasis.parallelepiped, volume, volumeForm
-/
theorem Orientation.measure_eq_volume (o : Orientation Real F (Fin n)) :
    o.volumeForm.measure = volume := by
  have A : o.volumeForm.measure (stdOrthonormalBasis Real F).toBasis.parallelepiped = 1 :=
    Orientation.measure_orthonormalBasis o (stdOrthonormalBasis Real F)
  rw [addHaarMeasure_unique o.volumeForm.measure
    (stdOrthonormalBasis Real F).toBasis.parallelepiped]; rw [A]; rw [one_smul]
  simp only [volume, Basis.addHaar]

end

/--
theorem `OrthonormalBasis.volume_parallelepiped` / 定理 `OrthonormalBasis.volume_parallelepiped`

English:
theorem OrthonormalBasis.volume_parallelepiped
  given: (b : OrthonormalBasis ι Real F)
  proof: by
  have : Fact (finrank Real F = finrank Real F) := ⟨rfl⟩
  let o := (stdOrthonormalBasis Real F).toBasis.orientation
  rw [← o.measure_eq_volume]
  exact o.measure_orthonormalBasis b

中文:
定理 正交标准基.volume_parallelepiped
  条件: (b : 正交标准基 ι 实数 F)
  证明: by
  have : Fact (finrank Real F = finrank Real F) := ⟨rfl⟩
  let o := (stdOrthonormalBasis Real F).toBasis.orientation
  rw [← o.measure_eq_volume]
  exact o.measure_orthonormalBasis b

Depends on / 依赖: finrank, measure_eq_volume, measure_orthonormalBasis, o.measure_eq_volume, o.measure_orthonormalBasis, orientation, stdOrthonormalBasis, toBasis, toBasis.orientation
-/
theorem OrthonormalBasis.volume_parallelepiped (b : OrthonormalBasis ι Real F) :
    volume (parallelepiped b) = 1 := by
  have : Fact (finrank Real F = finrank Real F) := ⟨rfl⟩
  let o := (stdOrthonormalBasis Real F).toBasis.orientation
  rw [← o.measure_eq_volume]
  exact o.measure_orthonormalBasis b

/--
theorem `OrthonormalBasis.addHaar_eq_volume` / 定理 `OrthonormalBasis.addHaar_eq_volume`

English:
theorem OrthonormalBasis.addHaar_eq_volume
  statement: {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
  proof: by
  rw [Basis.addHaar_eq_iff]
  exact b.volume_parallelepiped

中文:
定理 正交标准基.addHaar_eq_volume
  结论: {ι F : 类型} [有限类型 ι] [赋范交换加群 F]
  证明: by
  rw [Basis.addHaar_eq_iff]
  exact b.volume_parallelepiped

Depends on / 依赖: Basis.addHaar_eq_iff, addHaar_eq_iff, b.volume_parallelepiped, volume_parallelepiped
-/
theorem OrthonormalBasis.addHaar_eq_volume {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    [InnerProductSpace Real F] [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
    (b : OrthonormalBasis ι Real F) :
    b.toBasis.addHaar = volume := by
  rw [Basis.addHaar_eq_iff]
  exact b.volume_parallelepiped

/--
Definition of `OrthonormalBasis.measurableEquiv` / `OrthonormalBasis.measurableEquiv` 的定义

English:
definition OrthonormalBasis.measurableEquiv
  signature: (b : OrthonormalBasis ι Real F)
  body: b.repr.toHomeomorph.toMeasurableEquiv

中文:
定义 正交标准基.measurableEquiv
  签名: (b : 正交标准基 ι 实数 F)
  定义体: b.repr.toHomeomorph.toMeasurableEquiv

Depends on / 依赖: b.repr.toHomeomorph.toMeasurableEquiv, toHomeomorph, toMeasurableEquiv
-/
noncomputable def OrthonormalBasis.measurableEquiv (b : OrthonormalBasis ι Real F) :
    F ≃ᵐ EuclideanSpace Real ι := b.repr.toHomeomorph.toMeasurableEquiv

/--
theorem `OrthonormalBasis.measurePreserving_measurableEquiv` / 定理 `OrthonormalBasis.measurePreserving_measurableEquiv`

English:
theorem OrthonormalBasis.measurePreserving_measurableEquiv
  given: (b : OrthonormalBasis ι Real F)
  proof: by
  convert! (b.measurableEquiv.symm.measurable.measurePreserving _).symm
  rw [← (EuclideanSpace.basisFun ι Real).addHaar_eq_volume]
  erw [MeasurableEquiv.coe_toEquiv_symm, Basis.map_addHaar _ b.repr.symm.toContinuousLinearEquiv]
  exact b.addHaar_eq_volume.symm

中文:
定理 正交标准基.measurePreserving_measurableEquiv
  条件: (b : 正交标准基 ι 实数 F)
  证明: by
  convert! (b.measurableEquiv.symm.measurable.measurePreserving _).symm
  rw [← (EuclideanSpace.basisFun ι Real).addHaar_eq_volume]
  erw [MeasurableEquiv.coe_toEquiv_symm, Basis.map_addHaar _ b.repr.symm.toContinuousLinearEquiv]
  exact b.addHaar_eq_volume.symm

Depends on / 依赖: Basis.map_addHaar, EuclideanSpace, EuclideanSpace.basisFun, MeasurableEquiv, MeasurableEquiv.coe_toEquiv_symm, addHaar_eq_volume, b.addHaar_eq_volume.symm, b.measurableEquiv.symm.measurable.measurePreserving, b.repr.symm.toContinuousLinearEquiv, basisFun, coe_toEquiv_symm, convert, map_addHaar, measurable, measurableEquiv, measurePreserving, toContinuousLinearEquiv
-/
theorem OrthonormalBasis.measurePreserving_measurableEquiv (b : OrthonormalBasis ι Real F) :
    MeasurePreserving b.measurableEquiv volume volume := by
  convert! (b.measurableEquiv.symm.measurable.measurePreserving _).symm
  rw [← (EuclideanSpace.basisFun ι Real).addHaar_eq_volume]
  erw [MeasurableEquiv.coe_toEquiv_symm, Basis.map_addHaar _ b.repr.symm.toContinuousLinearEquiv]
  exact b.addHaar_eq_volume.symm

/--
theorem `OrthonormalBasis.measurePreserving_repr` / 定理 `OrthonormalBasis.measurePreserving_repr`

English:
theorem OrthonormalBasis.measurePreserving_repr
  given: (b : OrthonormalBasis ι Real F)
  proof: b.measurePreserving_measurableEquiv

中文:
定理 正交标准基.measurePreserving_repr
  条件: (b : 正交标准基 ι 实数 F)
  证明: b.measurePreserving_measurableEquiv

Depends on / 依赖: b.measurePreserving_measurableEquiv, measurePreserving_measurableEquiv
-/
theorem OrthonormalBasis.measurePreserving_repr (b : OrthonormalBasis ι Real F) :
    MeasurePreserving b.repr volume volume := b.measurePreserving_measurableEquiv

/--
theorem `OrthonormalBasis.measurePreserving_repr_symm` / 定理 `OrthonormalBasis.measurePreserving_repr_symm`

English:
theorem OrthonormalBasis.measurePreserving_repr_symm
  given: (b : OrthonormalBasis ι Real F)
  proof: b.measurePreserving_measurableEquiv.symm

中文:
定理 正交标准基.measurePreserving_repr_symm
  条件: (b : 正交标准基 ι 实数 F)
  证明: b.measurePreserving_measurableEquiv.symm

Depends on / 依赖: b.measurePreserving_measurableEquiv.symm, measurePreserving_measurableEquiv
-/
theorem OrthonormalBasis.measurePreserving_repr_symm (b : OrthonormalBasis ι Real F) :
    MeasurePreserving b.repr.symm volume volume := b.measurePreserving_measurableEquiv.symm

section PiLp

variable (ι : Type*)

variable [Fintype ι]

/--
theorem `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp` / 定理 `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`

English:
theorem EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
  proof: by
  suffices volume = map (MeasurableEquiv.toLp 2 (ι -> Real)) volume by
    convert! ((MeasurableEquiv.toLp 2 (ι -> Real)).measurable.measurePreserving _).symm
  rw [← addHaarMeasure_eq_volume_pi]; rw [← Basis.parallelepiped_basisFun]; rw [← Basis.addHaar_def]; rw [MeasurableEquiv.coe_toLp]; rw [←

中文:
定理 EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
  证明: by
  suffices volume = map (MeasurableEquiv.toLp 2 (ι -> Real)) volume by
    convert! ((MeasurableEquiv.toLp 2 (ι -> Real)).measurable.measurePreserving _).symm
  rw [← addHaarMeasure_eq_volume_pi]; rw [← Basis.parallelepiped_basisFun]; rw [← Basis.addHaar_def]; rw [MeasurableEquiv.coe_toLp]; rw [←

Depends on / 依赖: Basis.addHaar_def, Basis.map_addHaar, Basis.parallelepiped_basisFun, EuclideanSpace, EuclideanSpace.basisFun, MeasurableEquiv, MeasurableEquiv.coe_toLp, MeasurableEquiv.toLp, PiLp.coe_symm_continuousLinearEquiv, addHaarMeasure_eq_volume_pi, addHaar_def, addHaar_eq_volume, addHaar_eq_volume.symm, basisFun, coe_symm_continuousLinearEquiv, coe_toLp, convert, map_addHaar, measurable, measurable.measurePreserving
-/
theorem EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp :
    MeasurePreserving (MeasurableEquiv.toLp 2 (ι -> Real)).symm := by
  suffices volume = map (MeasurableEquiv.toLp 2 (ι -> Real)) volume by
    convert! ((MeasurableEquiv.toLp 2 (ι -> Real)).measurable.measurePreserving _).symm
  rw [← addHaarMeasure_eq_volume_pi]; rw [← Basis.parallelepiped_basisFun]; rw [← Basis.addHaar_def]; rw [MeasurableEquiv.coe_toLp]; rw [← PiLp.coe_symm_continuousLinearEquiv 2 Real]; rw [Basis.map_addHaar]
  exact (EuclideanSpace.basisFun _ _).addHaar_eq_volume.symm

/--
theorem `PiLp.volume_preserving_ofLp` / 定理 `PiLp.volume_preserving_ofLp`

English:
theorem PiLp.volume_preserving_ofLp
  statement: MeasurePreserving (@ofLp 2 (ι -> Real))
  proof: EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι

中文:
定理 PiLp.volume_preserving_ofLp
  结论: 保测 (@ofLp 2 (ι -> 实数))
  证明: EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι

Depends on / 依赖: EuclideanSpace, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, volume_preserving_symm_measurableEquiv_toLp
-/
theorem PiLp.volume_preserving_ofLp : MeasurePreserving (@ofLp 2 (ι -> Real)) :=
  EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι

/--
theorem `PiLp.volume_preserving_toLp` / 定理 `PiLp.volume_preserving_toLp`

English:
theorem PiLp.volume_preserving_toLp
  statement: MeasurePreserving (@toLp 2 (ι -> Real))
  proof: (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm

中文:
定理 PiLp.volume_preserving_toLp
  结论: 保测 (@toLp 2 (ι -> 实数))
  证明: (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm

Depends on / 依赖: EuclideanSpace, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, volume_preserving_symm_measurableEquiv_toLp
-/
theorem PiLp.volume_preserving_toLp : MeasurePreserving (@toLp 2 (ι -> Real)) :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm

/--
lemma `volume_euclideanSpace_eq_dirac` / 引理 `volume_euclideanSpace_eq_dirac`

English:
lemma volume_euclideanSpace_eq_dirac
  given: [IsEmpty ι]
  proof: by
  rw [← (PiLp.volume_preserving_toLp ι).map_eq]; rw [volume_pi_eq_dirac 0]; rw [map_dirac]; rw [toLp_zero]

中文:
引理 volume_euclideanSpace_eq_dirac
  条件: [是空 ι]
  证明: by
  rw [← (PiLp.volume_preserving_toLp ι).map_eq]; rw [volume_pi_eq_dirac 0]; rw [map_dirac]; rw [toLp_zero]

Depends on / 依赖: PiLp.volume_preserving_toLp, map_dirac, map_eq, toLp_zero, volume_pi_eq_dirac, volume_preserving_toLp
-/
lemma volume_euclideanSpace_eq_dirac [IsEmpty ι] :
    (volume : Measure (EuclideanSpace Real ι)) = Measure.dirac 0 := by
  rw [← (PiLp.volume_preserving_toLp ι).map_eq]; rw [volume_pi_eq_dirac 0]; rw [map_dirac]; rw [toLp_zero]

end PiLp

namespace LinearIsometryEquiv

/--
theorem `measurePreserving` / 定理 `measurePreserving`

English:
theorem measurePreserving
  given: (f : E ≃ₗᵢ[Real] F)
  proof: by
  refine ⟨f.continuous.measurable, ?_⟩
  rcases exists_orthonormalBasis Real E with ⟨w, b, _hw⟩
  erw [← OrthonormalBasis.addHaar_eq_volume b, ← OrthonormalBasis.addHaar_eq_volume (b.map f),
    Basis.map_addHaar _ f.toContinuousLinearEquiv]
  congr

中文:
定理 measurePreserving
  条件: (f : E ≃ₗᵢ[实数] F)
  证明: by
  refine ⟨f.continuous.measurable, ?_⟩
  rcases exists_orthonormalBasis Real E with ⟨w, b, _hw⟩
  erw [← OrthonormalBasis.addHaar_eq_volume b, ← OrthonormalBasis.addHaar_eq_volume (b.map f),
    Basis.map_addHaar _ f.toContinuousLinearEquiv]
  congr

Depends on / 依赖: Basis.map_addHaar, OrthonormalBasis, OrthonormalBasis.addHaar_eq_volume, addHaar_eq_volume, b.map, continuous, exists_orthonormalBasis, f.continuous.measurable, f.toContinuousLinearEquiv, map_addHaar, measurable, toContinuousLinearEquiv
-/
theorem measurePreserving (f : E ≃ₗᵢ[Real] F) :
    MeasurePreserving f := by
  refine ⟨f.continuous.measurable, ?_⟩
  rcases exists_orthonormalBasis Real E with ⟨w, b, _hw⟩
  erw [← OrthonormalBasis.addHaar_eq_volume b, ← OrthonormalBasis.addHaar_eq_volume (b.map f),
    Basis.map_addHaar _ f.toContinuousLinearEquiv]
  congr

end LinearIsometryEquiv

section Prod

variable (U V : Type*)
variable [NormedAddCommGroup U] [InnerProductSpace Real U] [MeasurableSpace U] [BorelSpace U]
variable [FiniteDimensional Real U]
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional Real V]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def volumePreservingSymmMeasurableEquivToLpProdAux
  body: ( -- WithLp 2 (U × V) ≃ₗᵢ[ℝ] WithLp 2 (WithLp 2 (Fin .. → ℝ) × WithLp 2 (Fin .. → ℝ)
    (LinearIsometryEquiv.withLpProdCongr 2
      (stdOrthonormalBasis Real U).repr
      (stdOrthonormalBasis Real V).repr).trans <|
    -- .. ≃ₗᵢ[ℝ] WithLp 2 (Fin (finrank ℝ U) ⊕ Fin (finrank ℝ V) → ℝ)
    (PiLp.su

中文:
定义 noncomputable
  签名: def volumePreservingSymmMeasurableEquivToLpProdAux
  定义体: ( -- WithLp 2 (U × V) ≃ₗᵢ[ℝ] WithLp 2 (WithLp 2 (Fin .. → ℝ) × WithLp 2 (Fin .. → ℝ)
    (LinearIsometryEquiv.withLpProdCongr 2
      (stdOrthonormalBasis Real U).repr
      (stdOrthonormalBasis Real V).repr).trans <|
    -- .. ≃ₗᵢ[ℝ] WithLp 2 (Fin (finrank ℝ U) ⊕ Fin (finrank ℝ V) → ℝ)
    (PiLp.su
-/
private noncomputable def volumePreservingSymmMeasurableEquivToLpProdAux :
    WithLp 2 (U × V) ≃ᵐ U × V :=
  ( -- WithLp 2 (U × V) ≃ₗᵢ[ℝ] WithLp 2 (WithLp 2 (Fin .. → ℝ) × WithLp 2 (Fin .. → ℝ)
    (LinearIsometryEquiv.withLpProdCongr 2
      (stdOrthonormalBasis Real U).repr
      (stdOrthonormalBasis Real V).repr).trans <|
    -- .. ≃ₗᵢ[ℝ] WithLp 2 (Fin (finrank ℝ U) ⊕ Fin (finrank ℝ V) → ℝ)
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ => Real)).symm
  ).toMeasurableEquiv.trans <|
  -- .. ≃ᵐ Fin (finrank ℝ U) ⊕ Fin (finrank ℝ V) → ℝ
(MeasurableEquiv.toLp 2 _).symm.trans
  -- .. ≃ᵐ Fin (finrank ℝ U) → ℝ × Fin (finrank ℝ V) → ℝ
(MeasurableEquiv.sumPiEquivProdPi (fun _ => Real)).trans
  -- .. ≃ᵐ U × V
  (MeasurableEquiv.prodCongr
    ((MeasurableEquiv.toLp 2 _).trans (stdOrthonormalBasis Real U).repr.symm.toMeasurableEquiv)
    ((MeasurableEquiv.toLp 2 _).trans (stdOrthonormalBasis Real V).repr.symm.toMeasurableEquiv))

/--
theorem `WithLp.volume_preserving_symm_measurableEquiv_toLp_prod` / 定理 `WithLp.volume_preserving_symm_measurableEquiv_toLp_prod`

English:
theorem WithLp.volume_preserving_symm_measurableEquiv_toLp_prod
  proof: by
  suffices MeasurePreserving (volumePreservingSymmMeasurableEquivToLpProdAux U V) by
    convert! this
    ext uv
    <;> simp [volumePreservingSymmMeasurableEquivToLpProdAux, MeasurableEquiv.coe_sumPiEquivProdPi,
      MeasurableEquiv.prodCongr]
  refine (LinearIsometryEquiv.measurePreserving _)

中文:
定理 WithLp.volume_preserving_symm_measurableEquiv_toLp_prod
  证明: by
  suffices MeasurePreserving (volumePreservingSymmMeasurableEquivToLpProdAux U V) by
    convert! this
    ext uv
    <;> simp [volumePreservingSymmMeasurableEquivToLpProdAux, MeasurableEquiv.coe_sumPiEquivProdPi,
      MeasurableEquiv.prodCongr]
  refine (LinearIsometryEquiv.measurePreserving _)

Depends on / 依赖: EuclideanSpace, EuclideanSpace.volume_, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, LinearIsometryEquiv, LinearIsometryEquiv.measurePreserving, MeasurableEquiv, MeasurableEquiv.coe_sumPiEquivProdPi, MeasurableEquiv.prodCongr, MeasurePreserving, MeasurePreserving.prod, all_goals, coe_sumPiEquivProdPi, convert, measurePreserving, measurePreserving_sumPiEquivProdPi, prodCongr, volumePreservingSymmMeasurableEquivToLpProdAux, volume_, volume_preserving_symm_measurableEquiv_toLp
-/
theorem WithLp.volume_preserving_symm_measurableEquiv_toLp_prod :
    MeasurePreserving (MeasurableEquiv.toLp 2 (U × V)).symm := by
  suffices MeasurePreserving (volumePreservingSymmMeasurableEquivToLpProdAux U V) by
    convert! this
    ext uv
    <;> simp [volumePreservingSymmMeasurableEquivToLpProdAux, MeasurableEquiv.coe_sumPiEquivProdPi,
      MeasurableEquiv.prodCongr]
  refine (LinearIsometryEquiv.measurePreserving _).trans ?_
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).trans ?_
  refine (measurePreserving_sumPiEquivProdPi _).trans ?_
  refine MeasurePreserving.prod ?_ ?_
  all_goals
  · refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm.trans ?_
    exact (LinearIsometryEquiv.measurePreserving _)

/--
theorem `WithLp.volume_preserving_ofLp` / 定理 `WithLp.volume_preserving_ofLp`

English:
theorem WithLp.volume_preserving_ofLp
  statement: MeasurePreserving (@ofLp 2 (U × V))
  proof: volume_preserving_symm_measurableEquiv_toLp_prod U V

中文:
定理 WithLp.volume_preserving_ofLp
  结论: 保测 (@ofLp 2 (U × V))
  证明: volume_preserving_symm_measurableEquiv_toLp_prod U V

Depends on / 依赖: volume_preserving_symm_measurableEquiv_toLp_prod
-/
theorem WithLp.volume_preserving_ofLp : MeasurePreserving (@ofLp 2 (U × V)) :=
  volume_preserving_symm_measurableEquiv_toLp_prod U V

/--
theorem `WithLp.volume_preserving_toLp` / 定理 `WithLp.volume_preserving_toLp`

English:
theorem WithLp.volume_preserving_toLp
  statement: MeasurePreserving (@toLp 2 (U × V))
  proof: (volume_preserving_symm_measurableEquiv_toLp_prod U V).symm

中文:
定理 WithLp.volume_preserving_toLp
  结论: 保测 (@toLp 2 (U × V))
  证明: (volume_preserving_symm_measurableEquiv_toLp_prod U V).symm

Depends on / 依赖: volume_preserving_symm_measurableEquiv_toLp_prod
-/
theorem WithLp.volume_preserving_toLp : MeasurePreserving (@toLp 2 (U × V)) :=
  (volume_preserving_symm_measurableEquiv_toLp_prod U V).symm

end Prod

/--
theorem `MeasureTheory.volume_eq_of_finrank_eq_one` / 定理 `MeasureTheory.volume_eq_of_finrank_eq_one`

English:
theorem MeasureTheory.volume_eq_of_finrank_eq_one
  statement: (h : Module.finrank Real E = 1) {v : E}
  proof: calc
  volume = ((volume : Measure Real).map (‖v‖⁻¹ • ·)).map (· • v) := by
    have hv' : Submodule.span Real {‖v‖⁻¹ • v} = ⊤ := by
      rw [Submodule.span_singleton_eq_top_iff]
      apply exists_smul_eq_of_finrank_eq_one h
      simpa
    let f : Real ≃ₗᵢ[Real] E := (LinearIsometryEquiv.toSpanUn

中文:
定理 测度论.volume_eq_of_finrank_eq_one
  结论: (h : 模.finrank 实数 E = 1) {v : E}
  证明: calc
  volume = ((volume : Measure Real).map (‖v‖⁻¹ • ·)).map (· • v) := by
    have hv' : Submodule.span Real {‖v‖⁻¹ • v} = ⊤ := by
      rw [Submodule.span_singleton_eq_top_iff]
      apply exists_smul_eq_of_finrank_eq_one h
      simpa
    let f : Real ≃ₗᵢ[Real] E := (LinearIsometryEquiv.toSpanUn
-/
theorem MeasureTheory.volume_eq_of_finrank_eq_one (h : Module.finrank Real E = 1) {v : E}
    (hv : v != 0) : (volume : Measure E) = ‖v‖ₑ • (volume : Measure Real).map (· • v) := calc
  volume = ((volume : Measure Real).map (‖v‖⁻¹ • ·)).map (· • v) := by
    have hv' : Submodule.span Real {‖v‖⁻¹ • v} = ⊤ := by
      rw [Submodule.span_singleton_eq_top_iff]
      apply exists_smul_eq_of_finrank_eq_one h
      simpa
    let f : Real ≃ₗᵢ[Real] E := (LinearIsometryEquiv.toSpanUnitSingleton (‖v‖⁻¹ • v)
      (by simp [norm_smul, hv])).trans (LinearIsometryEquiv.ofTop E _ hv')
    rw [map_map (by fun_prop) (by fun_prop)]
    convert! f.measurePreserving.map_eq.symm
    ext x
    simp [f, mul_comm, smul_smul]
  _ = ‖v‖ₑ • (volume : Measure Real).map (· • v) := by
    rw [map_addHaar_smul _ (by simpa using hv)]
    simp
