/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Covolume of ℤ-lattices

Let `E` be a finite-dimensional real vector space.

Let `L` be a `ℤ`-lattice `L` defined as a discrete `ℤ`-submodule of `E` that spans `E` over `ℝ`.

## Main definitions and results

* `ZLattice.covolume`: the covolume of `L` defined as the volume of an arbitrary fundamental
  domain of `L`.

* `ZLattice.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
  choice of the fundamental domain of `L`.

* `ZLattice.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
  value of the determinant of any `ℤ`-basis of `L`.

* `ZLattice.covolume_div_covolume_eq_relIndex`: Let `L₁` be a sub-`ℤ`-lattice of `L₂`. Then the
  index of `L₁` inside `L₂` is equal to `covolume L₁ / covolume L₂`.

* `ZLattice.covolume.tendsto_card_div_pow`: Let `s` be a bounded measurable set of `ι → ℝ`, then
  the number of points in `s ∩ n⁻¹ • L` divided by `n ^ card ι` tends to `volume s / covolume L`
  when `n : ℕ` tends to infinity.
  See also `ZLattice.covolume.tendsto_card_div_pow'` for a version for `InnerProductSpace ℝ E` and
  `ZLattice.covolume.tendsto_card_div_pow''` for the general version.

* `ZLattice.covolume.tendsto_card_le_div`: Let `X` be a cone in `ι → ℝ` and let `F : (ι → ℝ) → ℝ`
  be a function such that `F (c • x) = c ^ card ι * F x`. Then the number of points `x ∈ X` such
  that `F x ≤ c` divided by `c` tends to `volume {x ∈ X | F x ≤ 1} / covolume L`
  when `c : ℝ` tends to infinity.
  See also `ZLattice.covolume.tendsto_card_le_div'` for a version for `InnerProductSpace ℝ E` and
  `ZLattice.covolume.tendsto_card_le_div''` for the general version.

## Naming convention

Some results are true in the case where the ambient finite-dimensional real vector space is the
pi-space `ι → ℝ` and in the case where it is an `InnerProductSpace`. We use the following
convention: the plain name is for the pi case, for e.g. `volume_image_eq_volume_div_covolume`. For
the same result in the `InnerProductSpace` case, we add a `prime`, for e.g.
`volume_image_eq_volume_div_covolume'`. When the same result exists in the
general case, we had two primes, e.g. `covolume.tendsto_card_div_pow''`.

-/

@[expose] public section

noncomputable section

namespace ZLattice

open Submodule MeasureTheory Module MeasureTheory Module ZSpan

section General

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (L : Submodule Int E)

/--
Definition of `covolume` / `covolume` 的定义

English:
definition covolume
  signature: (μ : Measure E := by volume_tac)
  body: (addCovolume L E μ).toReal

中文:
定义 covolume
  签名: (μ : 测度 E := by volume_tac)
  定义体: (addCovolume L E μ).toReal

Depends on / 依赖: addCovolume, toReal, volume_tac
-/
def covolume (μ : Measure E := by volume_tac) : Real := (addCovolume L E μ).toReal

end General

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L]
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

set_option backward.privateInPublic true in
/--
theorem `covolume_eq_measure_fundamentalDomain` / 定理 `covolume_eq_measure_fundamentalDomain`

English:
theorem covolume_eq_measure_fundamentalDomain
  given: {F : Set E} (h : IsAddFundamentalDomain L F μ)
  proof: by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  exact congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

中文:
定理 covolume_eq_measure_fundamentalDomain
  条件: {F : 集合 E} (h : 是加法FundamentalDomain L F μ)
  证明: by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  exact congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

Depends on / 依赖: ENNReal, ENNReal.toReal, L.toAddSubgroup, MeasurableVAdd, VAddInvariantMeasure, congr_arg, covolume_eq_volume, h.covolume_eq_volume, toAddSubgroup, toReal
-/
theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    covolume L μ = μ.real F := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  exact congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

set_option backward.privateInPublic true in
/--
theorem `covolume_ne_zero` / 定理 `covolume_ne_zero`

English:
theorem covolume_ne_zero
  statement: covolume L μ != 0
  proof: by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis Int L) μ)]; rw [measureReal_ne_zero_iff (ne_of_lt _)]
  · exact measure_fundamentalDomain_ne_zero _
  · exact Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)

中文:
定理 covolume_ne_zero
  结论: covolume L μ != 0
  证明: by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis Int L) μ)]; rw [measureReal_ne_zero_iff (ne_of_lt _)]
  · exact measure_fundamentalDomain_ne_zero _
  · exact Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)

Depends on / 依赖: Bornology, Bornology.IsBounded.measure_lt_top, Free.chooseBasis, IdemSemiring, IdemSemiring.toIsOrderedAddMonoid, IsBounded, IsOrderedAddMonoid, chooseBasis, covolume_eq_measure_fundamentalDomain, fundamentalDomain_isBounded, isAddFundamentalDomain, measureReal_ne_zero_iff, measure_fundamentalDomain_ne_zero, measure_lt_top, ne_of_lt, toIsOrderedAddMonoid
-/
theorem covolume_ne_zero : covolume L μ != 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis Int L) μ)]; rw [measureReal_ne_zero_iff (ne_of_lt _)]
  · exact measure_fundamentalDomain_ne_zero _
  · exact Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)

set_option backward.privateInPublic true in
/--
theorem `covolume_pos` / 定理 `covolume_pos`

English:
theorem covolume_pos
  statement: 0 < covolume L μ
  proof: lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

中文:
定理 covolume_pos
  结论: 0 < covolume L μ
  证明: lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

Depends on / 依赖: CanonicallyOrderedAdd, ENNReal, ENNReal.toReal_nonneg, IdemSemiring, IdemSemiring.toCanonicallyOrderedAdd, covolume_ne_zero, lt_of_le_of_ne, toCanonicallyOrderedAdd, toReal_nonneg
-/
theorem covolume_pos : 0 < covolume L μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

set_option backward.privateInPublic true in
/--
theorem `covolume_comap` / 定理 `covolume_comap`

English:
theorem covolume_comap
  statement: {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
  proof: by
  rw [covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain (Free.chooseBasis Int L) μ)]; rw [covolume_eq_measure_fundamentalDomain _ _ ((isAddFundamentalDomain
    ((Free.chooseBasis Int L).ofZLatticeComap Real L e.toLinearEquiv) ν))]; rw [← he.measureReal_preimage
    (fundamentalDo

中文:
定理 covolume_comap
  结论: {F : 类型} [赋范交换加群 F] [赋范空间 实数 F] [有限维 实数 F]
  证明: by
  rw [covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain (Free.chooseBasis Int L) μ)]; rw [covolume_eq_measure_fundamentalDomain _ _ ((isAddFundamentalDomain
    ((Free.chooseBasis Int L).ofZLatticeComap Real L e.toLinearEquiv) ν))]; rw [← he.measureReal_preimage
    (fundamentalDo

Depends on / 依赖: Free.chooseBasis, IdemSemiring, IdemSemiring.toMulLeftMono, IsAddHaarMeasure, Measure, Measure.IsAddHaarMeasure, MeasurePreserving, MulLeftMono, ZLattice, ZLattice.comap, chooseBasis, covolume, covolume_eq_measure_fundamentalDomain, e.toLinearEquiv, e.toLinearMap, fundamentalDomain_measurableSet, he.measureReal_preimage, isAddFundamentalDomain, measureReal_preimage, nullMeasurableSet
-/
theorem covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F := by volume_tac) [Measure.IsAddHaarMeasure ν]
    {e : F ≃L[Real] E} (he : MeasurePreserving e ν μ) :
    covolume (ZLattice.comap Real L e.toLinearMap) ν = covolume L μ := by
  rw [covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain (Free.chooseBasis Int L) μ)]; rw [covolume_eq_measure_fundamentalDomain _ _ ((isAddFundamentalDomain
    ((Free.chooseBasis Int L).ofZLatticeComap Real L e.toLinearEquiv) ν))]; rw [← he.measureReal_preimage
    (fundamentalDomain_measurableSet _).nullMeasurableSet]; rw [← e.image_symm_eq_preimage]; rw [← e.symm.coe_toLinearEquiv]; rw [map_fundamentalDomain]
  congr!
  ext; simp

set_option backward.privateInPublic true in
/--
theorem `covolume_eq_det_mul_measureReal` / 定理 `covolume_eq_det_mul_measureReal`

English:
theorem covolume_eq_det_mul_measureReal
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int L)
  proof: by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ)]; rw [measureReal_fundamentalDomain _ _ b₀]; rw [measureReal_congr (fundamentalDomain_ae_parallelepiped b₀ μ)]
  congr
  ext
  exact b.ofZLatticeBasis_apply Real L _

中文:
定理 covolume_eq_det_mul_measure实数
  结论: {ι : 类型} [有限类型 ι] [DecidableEq ι] (b : 基 ι 整数 L)
  证明: by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ)]; rw [measureReal_fundamentalDomain _ _ b₀]; rw [measureReal_congr (fundamentalDomain_ae_parallelepiped b₀ μ)]
  congr
  ext
  exact b.ofZLatticeBasis_apply Real L _

Depends on / 依赖: IdemSemiring, IdemSemiring.toMulRightMono, MulRightMono, b.ofZLatticeBasis_apply, covolume_eq_measure_fundamentalDomain, fundamentalDomain_ae_parallelepiped, isAddFundamentalDomain, measureReal_congr, measureReal_fundamentalDomain, ofZLatticeBasis_apply, toMulRightMono
-/
theorem covolume_eq_det_mul_measureReal {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int L)
    (b₀ : Basis ι Real E) :
    covolume L μ = |b₀.det ((↑) ∘ b)| * μ.real (fundamentalDomain b₀) := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ)]; rw [measureReal_fundamentalDomain _ _ b₀]; rw [measureReal_congr (fundamentalDomain_ae_parallelepiped b₀ μ)]
  congr
  ext
  exact b.ofZLatticeBasis_apply Real L _

/--
theorem `covolume_eq_det` / 定理 `covolume_eq_det`

English:
theorem covolume_eq_det
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule Int (ι -> Real))
  proof: by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume)]; rw [volume_real_fundamentalDomain]
  congr
  ext1
  exact b.ofZLatticeBasis_apply Real L _

中文:
定理 covolume_eq_det
  结论: {ι : 类型} [有限类型 ι] [DecidableEq ι] (L : 子模 整数 (ι -> 实数))
  证明: by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume)]; rw [volume_real_fundamentalDomain]
  congr
  ext1
  exact b.ofZLatticeBasis_apply Real L _

Depends on / 依赖: b.ofZLatticeBasis_apply, covolume_eq_measure_fundamentalDomain, isAddFundamentalDomain, ofZLatticeBasis_apply, volume, volume_real_fundamentalDomain
-/
theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule Int (ι -> Real))
    [DiscreteTopology L] [IsZLattice Real L] (b : Basis ι Int L) :
    covolume L = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume)]; rw [volume_real_fundamentalDomain]
  congr
  ext1
  exact b.ofZLatticeBasis_apply Real L _

/--
theorem `covolume_eq_det_inv` / 定理 `covolume_eq_det_inv`

English:
theorem covolume_eq_det_inv
  statement: {ι : Type*} [Fintype ι] (L : Submodule Int (ι -> Real))
  proof: by
  classical
  rw [covolume_eq_det L b]; rw [← Pi.basisFun_det_apply]; rw [show (((↑) : L -> _) ∘ ⇑b) =
    (b.ofZLatticeBasis Real) by ext; simp]; rw [← Basis.det_inv]; rw [← abs_inv]; rw [Units.val_inv_eq_inv_val]; rw [IsUnit.unit_spec]; rw [← Basis.det_basis]; rw [LinearEquiv.coe_det]
  rfl

中文:
定理 covolume_eq_det_inv
  结论: {ι : 类型} [有限类型 ι] (L : 子模 整数 (ι -> 实数))
  证明: by
  classical
  rw [covolume_eq_det L b]; rw [← Pi.basisFun_det_apply]; rw [show (((↑) : L -> _) ∘ ⇑b) =
    (b.ofZLatticeBasis Real) by ext; simp]; rw [← Basis.det_inv]; rw [← abs_inv]; rw [Units.val_inv_eq_inv_val]; rw [IsUnit.unit_spec]; rw [← Basis.det_basis]; rw [LinearEquiv.coe_det]
  rfl

Depends on / 依赖: Basis.det_basis, Basis.det_inv, IsUnit, IsUnit.unit_spec, LinearEquiv, LinearEquiv.coe_det, Pi.basisFun_det_apply, Units.val_inv_eq_inv_val, abs_inv, b.ofZLatticeBasis, basisFun_det_apply, classical, coe_det, covolume_eq_det, det_basis, det_inv, ofZLatticeBasis, unit_spec, val_inv_eq_inv_val
-/
theorem covolume_eq_det_inv {ι : Type*} [Fintype ι] (L : Submodule Int (ι -> Real))
    [DiscreteTopology L] [IsZLattice Real L] (b : Basis ι Int L) :
    covolume L = |(LinearEquiv.det (b.ofZLatticeBasis Real L).equivFun : Real)|⁻¹ := by
  classical
  rw [covolume_eq_det L b]; rw [← Pi.basisFun_det_apply]; rw [show (((↑) : L -> _) ∘ ⇑b) =
    (b.ofZLatticeBasis Real) by ext; simp]; rw [← Basis.det_inv]; rw [← abs_inv]; rw [Units.val_inv_eq_inv_val]; rw [IsUnit.unit_spec]; rw [← Basis.det_basis]; rw [LinearEquiv.coe_det]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `covolume_div_covolume_eq_relIndex` / 定理 `covolume_div_covolume_eq_relIndex`

English:
theorem covolume_div_covolume_eq_relIndex
  statement: {ι : Type*} [Fintype ι] (L₁ L₂ : Submodule Int (ι -> Real))
  proof: by
  classical
  let b₁ := IsZLattice.basis L₁
  let b₂ := IsZLattice.basis L₂
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂]; rw [Nat.cast_natAbs]; rw [Int.cast_abs]
  trans |(b₂.ofZLatticeBasis Real).det (b₁.ofZLatticeBasis Real)|
  · rw [← Basis.det_mul_det _ 

中文:
定理 covolume_div_covolume_eq_relIndex
  结论: {ι : 类型} [有限类型 ι] (L₁ L₂ : 子模 整数 (ι -> 实数))
  证明: by
  classical
  let b₁ := IsZLattice.basis L₁
  let b₂ := IsZLattice.basis L₂
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂]; rw [Nat.cast_natAbs]; rw [Int.cast_abs]
  trans |(b₂.ofZLatticeBasis Real).det (b₁.ofZLatticeBasis Real)|
  · rw [← Basis.det_mul_det _ 

Depends on / 依赖: AddSubgroup, AddSubgroup.relIndex_eq_natAbs_det, Basis.det_inv, Basis.det_mul_det, Int.cast_abs, IsUnit, IsUnit.unit_spec, IsZLattice, IsZLattice.basis, Nat.cast_natAbs, Pi.basisFun, Pi.basisFun_det_apply, Units.val_inv_eq_inv_val, abs_inv, abs_mul, basisFun, basisFun_det_apply, cast_abs, cast_natAbs, classical
-/
theorem covolume_div_covolume_eq_relIndex {ι : Type*} [Fintype ι] (L₁ L₂ : Submodule Int (ι -> Real))
    [DiscreteTopology L₁] [IsZLattice Real L₁] [DiscreteTopology L₂] [IsZLattice Real L₂] (h : L₁ <= L₂) :
    covolume L₁ / covolume L₂ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₁ := IsZLattice.basis L₁
  let b₂ := IsZLattice.basis L₂
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂]; rw [Nat.cast_natAbs]; rw [Int.cast_abs]
  trans |(b₂.ofZLatticeBasis Real).det (b₁.ofZLatticeBasis Real)|
  · rw [← Basis.det_mul_det _ (Pi.basisFun Real ι) _, abs_mul, Pi.basisFun_det_apply,
      ← Basis.det_inv, Units.val_inv_eq_inv_val, IsUnit.unit_spec, Pi.basisFun_det_apply,
      covolume_eq_det _ b₁, covolume_eq_det _ b₂, mul_comm, abs_inv]
    congr 3 <;> ext <;> simp
  · rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
    congr; ext i j
    rw [Matrix.map_apply]; rw [Basis.toMatrix_apply]; rw [Basis.toMatrix_apply]; rw [Basis.ofZLatticeBasis_apply]
    exact (b₂.ofZLatticeBasis_repr_apply Real L₂ ⟨b₁ j, h (coe_mem _)⟩ i)

/--
theorem `covolume_div_covolume_eq_relIndex'` / 定理 `covolume_div_covolume_eq_relIndex'`

English:
theorem covolume_div_covolume_eq_relIndex'
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  let f := (EuclideanSpace.equiv _ Real).symm.trans
    (stdOrthonormalBasis Real E).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f := (stdOrthonormalBasis Real E).measurePreserving_repr_symm.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm
  rw [← c

中文:
定理 covolume_div_covolume_eq_relIndex'
  结论: {E : 类型} [赋范交换加群 E]
  证明: by
  let f := (EuclideanSpace.equiv _ Real).symm.trans
    (stdOrthonormalBasis Real E).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f := (stdOrthonormalBasis Real E).measurePreserving_repr_symm.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm
  rw [← c

Depends on / 依赖: EuclideanSpace, EuclideanSpace.equiv, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, MeasurePreserving, ZLattice, ZLattice.comap_toAddSubgroup, comap_toAddSubgroup, covolume_comap, covolume_div_covolume_eq_relIndex, measurePreserving_repr_symm, measurePreserving_repr_symm.comp, repr.toContinuousLinearEquiv.symm, stdOrthonormalBasis, symm.trans, toContinuousLinearEquiv, volume, volume_preserving_symm_measurableEquiv_toLp
-/
theorem covolume_div_covolume_eq_relIndex' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
    (L₁ L₂ : Submodule Int E) [DiscreteTopology L₁] [IsZLattice Real L₁] [DiscreteTopology L₂]
    [IsZLattice Real L₂] (h : L₁ <= L₂) :
    covolume L₁ / covolume L₂ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  let f := (EuclideanSpace.equiv _ Real).symm.trans
    (stdOrthonormalBasis Real E).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f := (stdOrthonormalBasis Real E).measurePreserving_repr_symm.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm
  rw [← covolume_comap L₁ volume volume hf]; rw [← covolume_comap L₂ volume volume hf]; rw [covolume_div_covolume_eq_relIndex _ _ (fun _ h' => h h')]; rw [ZLattice.comap_toAddSubgroup]; rw [ZLattice.comap_toAddSubgroup]; rw [Nat.cast_inj]; rw [LinearEquiv.toAddMonoidHom_commutes]; rw [AddSubgroup.comap_equiv_eq_map_symm']; rw [AddSubgroup.comap_equiv_eq_map_symm']; rw [AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]

/--
theorem `volume_image_eq_volume_div_covolume` / 定理 `volume_image_eq_volume_div_covolume`

English:
theorem volume_image_eq_volume_div_covolume
  statement: {ι : Type*} [Fintype ι] (L : Submodule Int (ι -> Real))
  proof: by
  rw [LinearEquiv.image_eq_preimage_symm]; rw [Measure.addHaar_preimage_linearEquiv]; rw [LinearEquiv.symm_symm]; rw [covolume_eq_det_inv L b]; rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.ofReal_inv_of_pos (abs_pos.2 (LinearEquiv.det _).ne_zero)]; rw [inv_inv]; rw [LinearEquiv.coe_det]

中文:
定理 volume_image_eq_volume_div_covolume
  结论: {ι : 类型} [有限类型 ι] (L : 子模 整数 (ι -> 实数))
  证明: by
  rw [LinearEquiv.image_eq_preimage_symm]; rw [Measure.addHaar_preimage_linearEquiv]; rw [LinearEquiv.symm_symm]; rw [covolume_eq_det_inv L b]; rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.ofReal_inv_of_pos (abs_pos.2 (LinearEquiv.det _).ne_zero)]; rw [inv_inv]; rw [LinearEquiv.coe_det]

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, ENNReal.ofReal_inv_of_pos, LinearEquiv, LinearEquiv.coe_det, LinearEquiv.det, LinearEquiv.image_eq_preimage_symm, LinearEquiv.symm_symm, Measure, Measure.addHaar_preimage_linearEquiv, abs_pos, addHaar_preimage_linearEquiv, coe_det, covolume_eq_det_inv, div_eq_inv_mul, image_eq_preimage_symm, inv_inv, ne_zero, ofReal_inv_of_pos, symm_symm
-/
theorem volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι] (L : Submodule Int (ι -> Real))
    [DiscreteTopology L] [IsZLattice Real L] (b : Basis ι Int L) {s : Set (ι -> Real)} :
    volume ((b.ofZLatticeBasis Real L).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  rw [LinearEquiv.image_eq_preimage_symm]; rw [Measure.addHaar_preimage_linearEquiv]; rw [LinearEquiv.symm_symm]; rw [covolume_eq_det_inv L b]; rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.ofReal_inv_of_pos (abs_pos.2 (LinearEquiv.det _).ne_zero)]; rw [inv_inv]; rw [LinearEquiv.coe_det]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `volume_image_eq_volume_div_covolume'` / 定理 `volume_image_eq_volume_div_covolume'`

English:
theorem volume_image_eq_volume_div_covolume'
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  let e : Fin (finrank Real E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZLatticeBasis Real)])
  let f := (EuclideanSpace.equiv ι Real).symm.trans
    ((stdOrthonormalBasis Real E).reindex e).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreservi

中文:
定理 volume_image_eq_volume_div_covolume'
  结论: {E : 类型} [赋范交换加群 E]
  证明: by
  let e : Fin (finrank Real E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZLatticeBasis Real)])
  let f := (EuclideanSpace.equiv ι Real).symm.trans
    ((stdOrthonormalBasis Real E).reindex e).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreservi

Depends on / 依赖: EuclideanSpace, EuclideanSpace.equiv, Fintype, Fintype.card_fin, Fintype.equivOfCardEq, MeasurePreserving, PiLp.volume_preserving_toLp, b.ofZLatticeBasis, card_fin, covolume_comap, equivOfCardEq, finrank, finrank_eq_card_basis, hf.measure_preimage, measurePreserving_repr_symm, measurePreserving_repr_symm.comp, measure_preimage, ofZLatticeBasis, reindex, repr.toContinuousLinearEquiv.symm
-/
theorem volume_image_eq_volume_div_covolume' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L] {ι : Type*} [Fintype ι]
    (b : Basis ι Int L) {s : Set E} (hs : NullMeasurableSet s) :
    volume ((b.ofZLatticeBasis Real).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  let e : Fin (finrank Real E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZLatticeBasis Real)])
  let f := (EuclideanSpace.equiv ι Real).symm.trans
    ((stdOrthonormalBasis Real E).reindex e).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f :=
    ((stdOrthonormalBasis Real E).reindex e).measurePreserving_repr_symm.comp
      (PiLp.volume_preserving_toLp ι)
  rw [← hf.measure_preimage hs]; rw [← (covolume_comap L volume volume hf)]; rw [← volume_image_eq_volume_div_covolume (ZLattice.comap Real L f.toLinearMap)
    (b.ofZLatticeComap Real L f.toLinearEquiv)]; rw [Basis.ofZLatticeBasis_comap]; rw [← f.image_symm_eq_preimage]; rw [← Set.image_comp]
  simp

end Basic

namespace covolume

section General

open Filter Fintype Pointwise Topology BoxIntegral Bornology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {L : Submodule Int E} [DiscreteTopology L] [IsZLattice Real L]
variable {ι : Type*} [Fintype ι] (b : Basis ι Int L)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tendsto_card_div_pow''` / 定理 `tendsto_card_div_pow''`

English:
theorem tendsto_card_div_pow''
  statement: [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
  proof: by
  refine Tendsto.congr' ?_
    (tendsto_card_div_pow_atTop_volume ((b.ofZLatticeBasis Real).equivFun '' s) ?_ ?_ hs₃)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    congr
refine Nat.card_congr ((b.ofZLatticeBasis Real).equivFun.toEquiv.subtypeEquiv fun x => ?_).symm
    simp_rw [Set.mem

中文:
定理 tendsto_card_div_pow''
  结论: [有限维 实数 E] [可测空间 E] [Borel空间 E]
  证明: by
  refine Tendsto.congr' ?_
    (tendsto_card_div_pow_atTop_volume ((b.ofZLatticeBasis Real).equivFun '' s) ?_ ?_ hs₃)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    congr
refine Nat.card_congr ((b.ofZLatticeBasis Real).equivFun.toEquiv.subtypeEquiv fun x => ?_).symm
    simp_rw [Set.mem

Depends on / 依赖: Basis.equivFun_apply, DFunLike, DFunLike.coe_fn_eq, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, LinearEquiv, LinearEquiv.coe_toEquiv, Nat.card_congr, Set.mem_image, Set.mem_inter_iff, Set.mem_inv_smul_set_i, Tendsto, Tendsto.congr, and_congr_right_iff, apply_eq_iff_eq, b.ofZLatticeBasis, b.ofZLatticeBasis_span, card_congr, coe_fn_eq, coe_toEquiv
-/
theorem tendsto_card_div_pow'' [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier ((b.ofZLatticeBasis Real).equivFun '' s)) = 0) :
    Tendsto (fun n : Nat => (Nat.card (s inter (n : Real)⁻¹ • L : Set E) : Real) / n ^ card ι)
      atTop (𝓝 (volume.real ((b.ofZLatticeBasis Real).equivFun '' s))) := by
  refine Tendsto.congr' ?_
    (tendsto_card_div_pow_atTop_volume ((b.ofZLatticeBasis Real).equivFun '' s) ?_ ?_ hs₃)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    congr
refine Nat.card_congr ((b.ofZLatticeBasis Real).equivFun.toEquiv.subtypeEquiv fun x => ?_).symm
    simp_rw [Set.mem_inter_iff, ← b.ofZLatticeBasis_span Real, LinearEquiv.coe_toEquiv,
      Basis.equivFun_apply, Set.mem_image, DFunLike.coe_fn_eq, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, and_congr_right_iff, Set.mem_inv_smul_set_iff₀
      (mod_cast hn.ne' : (n : Real) != 0), ← Finsupp.coe_smul, ← map_smul, SetLike.mem_coe,
      Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff Real] at hs₁ ⊢
    exact Bornology.IsVonNBounded.image hs₁ ((b.ofZLatticeBasis Real).equivFunL : E ->L[Real] ι -> Real)
  · exact (b.ofZLatticeBasis Real).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs₂

/--
theorem `tendsto_card_le_div''_aux` / 定理 `tendsto_card_le_div''_aux`

English:
theorem tendsto_card_le_div''_aux
  proof: by
  ext x
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_ofPred_eq, hF₁ _
    (inv_pos_of_pos hc).le, inv_pow, inv_mul_le_iff₀ (pow_pos hc _), mul_one, and_congr_left_iff]
  exact fun _ => ⟨fun h => (smul_inv_smul₀ hc.ne' x) ▸ hX h hc, fun h => hX h (inv_pos_of_pos hc)⟩

中文:
定理 tendsto_card_le_div''_aux
  证明: by
  ext x
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_ofPred_eq, hF₁ _
    (inv_pos_of_pos hc).le, inv_pow, inv_mul_le_iff₀ (pow_pos hc _), mul_one, and_congr_left_iff]
  exact fun _ => ⟨fun h => (smul_inv_smul₀ hc.ne' x) ▸ hX h hc, fun h => hX h (inv_pos_of_pos hc)⟩
-/
private theorem tendsto_card_le_div''_aux
    {X : Set E} (hX : forall ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r -> r • x in X)
    {F : E -> Real} (hF₁ : forall x ⦃r : Real⦄, 0 <= r -> F (r • x) = r ^ card ι * (F x)) {c : Real} (hc : 0 < c) :
    c • {x in X | F x <= 1} = {x in X | F x <= c ^ card ι} := by
  ext x
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_ofPred_eq, hF₁ _
    (inv_pos_of_pos hc).le, inv_pow, inv_mul_le_iff₀ (pow_pos hc _), mul_one, and_congr_left_iff]
  exact fun _ => ⟨fun h => (smul_inv_smul₀ hc.ne' x) ▸ hX h hc, fun h => hX h (inv_pos_of_pos hc)⟩

/--
theorem `tendsto_card_le_div''` / 定理 `tendsto_card_le_div''`

English:
theorem tendsto_card_le_div''
  statement: [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
  proof: by
refine Tendsto.congr' ?_ (tendsto_card_div_pow_atTop_volume'
      ((b.ofZLatticeBasis Real).equivFun '' {x in X | F x <= 1}) ?_ ?_ h₄ fun x y hx hy => ?_).comp
        (tendsto_rpow_atTop <| inv_pos.mpr
          (Nat.cast_pos.mpr card_pos) : Tendsto (fun x => x ^ (card ι : Real)⁻¹) atTop atTop)

中文:
定理 tendsto_card_le_div''
  结论: [有限维 实数 E] [可测空间 E] [Borel空间 E]
  证明: by
refine Tendsto.congr' ?_ (tendsto_card_div_pow_atTop_volume'
      ((b.ofZLatticeBasis Real).equivFun '' {x in X | F x <= 1}) ?_ ?_ h₄ fun x y hx hy => ?_).comp
        (tendsto_rpow_atTop <| inv_pos.mpr
          (Nat.cast_pos.mpr card_pos) : Tendsto (fun x => x ^ (card ι : Real)⁻¹) atTop atTop)

Depends on / 依赖: Nat.cast_ne_zero.mpr, Nat.cast_pos.mpr, Real.rpow_pos_of_pos, Tendsto, Tendsto.congr, b.ofZLatticeBasis, card_ne_zero, card_pos, cast_ne_zero, cast_pos, equivFun, eventually_gt_atTop, filter_upwards, inv_pos, inv_pos.mpr, ofZLatticeBasis, rpow_pos_of_pos, tendsto_card_div_pow_atTop_volume, tendsto_rpow_atTop
-/
theorem tendsto_card_le_div'' [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
    [Nonempty ι] {X : Set E} (hX : forall ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r -> r • x in X)
    {F : E -> Real} (h₁ : forall x ⦃r : Real⦄, 0 <= r -> F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x in X | F x <= 1}) (h₃ : MeasurableSet {x in X | F x <= 1})
    (h₄ : volume (frontier ((b.ofZLatticeBasis Real L).equivFun '' {x | x in X ∧ F x <= 1})) = 0) :
    Tendsto (fun c : Real =>
      Nat.card ({x in X | F x <= c} inter L : Set E) / (c : Real))
        atTop (𝓝 (volume.real ((b.ofZLatticeBasis Real).equivFun '' {x in X | F x <= 1}))) := by
refine Tendsto.congr' ?_ (tendsto_card_div_pow_atTop_volume'
      ((b.ofZLatticeBasis Real).equivFun '' {x in X | F x <= 1}) ?_ ?_ h₄ fun x y hx hy => ?_).comp
        (tendsto_rpow_atTop <| inv_pos.mpr
          (Nat.cast_pos.mpr card_pos) : Tendsto (fun x => x ^ (card ι : Real)⁻¹) atTop atTop)
  · filter_upwards [eventually_gt_atTop 0] with c hc
    have aux₁ : (card ι : Real) != 0 := Nat.cast_ne_zero.mpr card_ne_zero
    have aux₂ : 0 < c ^ (card ι : Real)⁻¹ := Real.rpow_pos_of_pos hc _
    have aux₃ : (c ^ (card ι : Real)⁻¹)⁻¹ != 0 := inv_ne_zero aux₂.ne'
    have aux₄ : c ^ (-(card ι : Real)⁻¹) != 0 := (Real.rpow_pos_of_pos hc _).ne'
    obtain ⟨hc₁, hc₂⟩ := lt_iff_le_and_ne.mp hc
    rw [Function.comp_apply]; rw [← Real.rpow_natCast]; rw [Real.rpow_inv_rpow hc₁ aux₁]; rw [eq_comm]
    congr
refine Nat.card_congr Equiv.subtypeEquiv ((b.ofZLatticeBasis Real).equivFun.toEquiv.trans
          (Equiv.smulRight aux₄)) fun _ => ?_
    rw [Set.mem_inter_iff]; rw [Set.mem_inter_iff]; rw [Equiv.trans_apply]; rw [LinearEquiv.coe_toEquiv]; rw [Equiv.smulRight_apply]; rw [Real.rpow_neg hc₁]; rw [Set.smul_mem_smul_set_iff₀ aux₃]; rw [← Set.mem_smul_set_iff_inv_smul_mem₀ aux₂.ne']; rw [← image_smul_set]; rw [tendsto_card_le_div''_aux hX h₁ aux₂]; rw [← Real.rpow_natCast]; rw [← Real.rpow_mul hc₁]; rw [inv_mul_cancel₀ aux₁]; rw [Real.rpow_one]
    simp_rw [SetLike.mem_coe, Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
      and_congr_right_iff, ← b.ofZLatticeBasis_span Real, Basis.mem_span_iff_repr_mem,
      Pi.basisFun_repr, Basis.equivFun_apply, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff Real] at h₂ ⊢
    exact Bornology.IsVonNBounded.image h₂ ((b.ofZLatticeBasis Real).equivFunL : E ->L[Real] ι -> Real)
  · exact (b.ofZLatticeBasis Real).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr h₃
  · simp_rw [← image_smul_set]
    apply Set.image_mono
    rw [tendsto_card_le_div''_aux hX h₁ hx]; rw [tendsto_card_le_div''_aux hX h₁ (lt_of_lt_of_le hx hy)]
exact fun a ⟨ha₁, ha₂⟩ => ⟨ha₁, le_trans ha₂ pow_le_pow_left₀ (le_of_lt hx) hy _⟩

end General

section Pi

open Filter Fintype Pointwise Topology Bornology

/--
theorem `frontier_equivFun` / 定理 `frontier_equivFun`

English:
theorem frontier_equivFun
  statement: {E : Type*} [AddCommGroup E] [Module Real E] {ι : Type*} [Finite ι]
  proof: by
  rw [LinearEquiv.image_eq_preimage_symm]; rw [LinearEquiv.image_eq_preimage_symm]
  exact (Homeomorph.preimage_frontier b.equivFunL.toHomeomorph.symm s).symm

中文:
定理 frontier_equivFun
  结论: {E : 类型} [加法交换群 E] [模 实数 E] {ι : 类型} [有限 ι]
  证明: by
  rw [LinearEquiv.image_eq_preimage_symm]; rw [LinearEquiv.image_eq_preimage_symm]
  exact (Homeomorph.preimage_frontier b.equivFunL.toHomeomorph.symm s).symm
-/
private theorem frontier_equivFun {E : Type*} [AddCommGroup E] [Module Real E] {ι : Type*} [Finite ι]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul Real E] [T2Space E]
    (b : Basis ι Real E) (s : Set E) :
    frontier (b.equivFun '' s) = b.equivFun '' (frontier s) := by
  rw [LinearEquiv.image_eq_preimage_symm]; rw [LinearEquiv.image_eq_preimage_symm]
  exact (Homeomorph.preimage_frontier b.equivFunL.toHomeomorph.symm s).symm

variable {ι : Type*} [Fintype ι]
variable (L : Submodule Int (ι -> Real)) [DiscreteTopology L] [IsZLattice Real L]

/--
theorem `tendsto_card_div_pow` / 定理 `tendsto_card_div_pow`

English:
theorem tendsto_card_div_pow
  statement: (b : Basis ι Int L) {s : Set (ι -> Real)} (hs₁ : IsBounded s)
  proof: by
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b]; rw [ENNReal.toReal_div]; rw [ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume, hs₃, ENNReal.zero_div]

中文:
定理 tendsto_card_div_pow
  结论: (b : 基 ι 整数 L) {s : 集合 (ι -> 实数)} (hs₁ : IsBounded s)
  证明: by
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b]; rw [ENNReal.toReal_div]; rw [ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume, hs₃, ENNReal.zero_div]

Depends on / 依赖: ENNReal, ENNReal.toReal_div, ENNReal.toReal_ofReal, ENNReal.zero_div, convert, covolume_pos, frontier_equivFun, measureReal_def, tendsto_card_div_pow, toReal_div, toReal_ofReal, volume, volume_image_eq_volume_div_covolume, zero_div
-/
theorem tendsto_card_div_pow (b : Basis ι Int L) {s : Set (ι -> Real)} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : Nat => (Nat.card (s inter (n : Real)⁻¹ • L : Set (ι -> Real)) : Real) / n ^ card ι)
      atTop (𝓝 (volume.real s / covolume L)) := by
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b]; rw [ENNReal.toReal_div]; rw [ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume, hs₃, ENNReal.zero_div]

/--
theorem `tendsto_card_le_div` / 定理 `tendsto_card_le_div`

English:
theorem tendsto_card_le_div
  statement: {X : Set (ι -> Real)} (hX : forall ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r -> r • x in X)
  proof: by
  let e : Free.ChooseBasisIndex Int ↥L ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [ZLattice.rank Real]; rw [finrank_fintype_fun_eq_card]
  let b := (Module.Free.chooseBasis Int L).reindex e
  convert! tendsto_card_le_div'' b hX h₁ h₂ h₃ ?_
  · si

中文:
定理 tendsto_card_le_div
  结论: {X : 集合 (ι -> 实数)} (hX : 对任意 ⦃x⦄ ⦃r : 实数⦄, x in X -> 0 < r -> r • x in X)
  证明: by
  let e : Free.ChooseBasisIndex Int ↥L ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [ZLattice.rank Real]; rw [finrank_fintype_fun_eq_card]
  let b := (Module.Free.chooseBasis Int L).reindex e
  convert! tendsto_card_le_div'' b hX h₁ h₂ h₃ ?_
  · si

Depends on / 依赖: ChooseBasisIndex, ENNReal, ENNReal.toReal_div, ENNReal.toReal_ofReal, Fintype, Fintype.equivOfCardEq, Free.ChooseBasisIndex, Module, Module.Free.chooseBasis, ZLattice, ZLattice.rank, chooseBasis, convert, covolume_pos, equivOfCardEq, finrank_eq_card_chooseBasisIndex, finrank_fintype_fun_eq_card, frontier_equivFun, measureReal_def, reindex
-/
theorem tendsto_card_le_div {X : Set (ι -> Real)} (hX : forall ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r -> r • x in X)
    {F : (ι -> Real) -> Real} (h₁ : forall x ⦃r : Real⦄, 0 <= r -> F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x in X | F x <= 1}) (h₃ : MeasurableSet {x in X | F x <= 1})
    (h₄ : volume (frontier {x | x in X ∧ F x <= 1}) = 0) [Nonempty ι] :
    Tendsto (fun c : Real =>
      Nat.card ({x in X | F x <= c} inter L : Set (ι -> Real)) / (c : Real))
        atTop (𝓝 (volume.real {x in X | F x <= 1} / covolume L)) := by
  let e : Free.ChooseBasisIndex Int ↥L ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [ZLattice.rank Real]; rw [finrank_fintype_fun_eq_card]
  let b := (Module.Free.chooseBasis Int L).reindex e
  convert! tendsto_card_le_div'' b hX h₁ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b]; rw [ENNReal.toReal_div]; rw [ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume, h₄, ENNReal.zero_div]

end Pi

section InnerProductSpace

open Filter Pointwise Topology Bornology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L]

/--
theorem `tendsto_card_div_pow'` / 定理 `tendsto_card_div_pow'`

English:
theorem tendsto_card_div_pow'
  statement: {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
  proof: by
  let b := Module.Free.chooseBasis Int L
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank Real L]
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b hs₂.nullMeasurableSet]; rw [ENNReal.toReal_div]; rw [ENNReal.t

中文:
定理 tendsto_card_div_pow'
  结论: {s : 集合 E} (hs₁ : IsBounded s) (hs₂ : 可测集 s)
  证明: by
  let b := Module.Free.chooseBasis Int L
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank Real L]
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b hs₂.nullMeasurableSet]; rw [ENNReal.toReal_div]; rw [ENNReal.t

Depends on / 依赖: ENNReal, ENNReal.toReal_div, ENNReal.toReal_ofReal, ENNReal.zero_div, Module, Module.Free.chooseBasis, NullMeasurableSet, NullMeasurableSet.of_null, ZLattice, ZLattice.rank, chooseBasis, convert, covolume_pos, finrank_eq_card_chooseBasisIndex, frontier_equivFun, measureReal_def, nullMeasurableSet, of_null, tendsto_card_div_pow, toReal_div
-/
theorem tendsto_card_div_pow' {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : Nat => (Nat.card (s inter (n : Real)⁻¹ • L : Set E) : Real) / n ^ finrank Real E)
      atTop (𝓝 (volume.real s / covolume L)) := by
  let b := Module.Free.chooseBasis Int L
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank Real L]
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b hs₂.nullMeasurableSet]; rw [ENNReal.toReal_div]; rw [ENNReal.toReal_ofReal (covolume_pos L volume).le]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume', hs₃, ENNReal.zero_div]
    exact NullMeasurableSet.of_null hs₃

/--
theorem `tendsto_card_le_div'` / 定理 `tendsto_card_le_div'`

English:
theorem tendsto_card_le_div'
  statement: [Nontrivial E] {X : Set E} {F : E -> Real}
  proof: by
  let b := Module.Free.chooseBasis Int L
  convert! tendsto_card_le_div'' b hX ?_ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b h₃.nullMeasurableSet]; rw [ENNReal.toReal_div]; rw [ENNReal.toReal_ofReal (covolume_pos L volume).le]
· have : Nontrivial L :

中文:
定理 tendsto_card_le_div'
  结论: [非平凡 E] {X : 集合 E} {F : E -> 实数}
  证明: by
  let b := Module.Free.chooseBasis Int L
  convert! tendsto_card_le_div'' b hX ?_ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b h₃.nullMeasurableSet]; rw [ENNReal.toReal_div]; rw [ENNReal.toReal_ofReal (covolume_pos L volume).le]
· have : Nontrivial L :

Depends on / 依赖: ENNReal, ENNReal.toReal_div, ENNReal.toReal_ofReal, Module, Module.Free.chooseBasis, Nontrivial, ZLattice, ZLattice.rank, chooseBasis, convert, covolume_pos, finrank_eq_card_chooseBasisIndex, finrank_pos, frontier_equivFun, infer_instance, measureReal_def, nontrivial_of_finrank_pos, nullMeasurableSet, tendsto_card_le_div, toReal_div
-/
theorem tendsto_card_le_div' [Nontrivial E] {X : Set E} {F : E -> Real}
    (hX : forall ⦃x⦄ ⦃r : Real⦄, x in X -> 0 < r -> r • x in X)
    (h₁ : forall x ⦃r : Real⦄, 0 <= r -> F (r • x) = r ^ finrank Real E * (F x))
    (h₂ : IsBounded {x in X | F x <= 1}) (h₃ : MeasurableSet {x in X | F x <= 1})
    (h₄ : volume (frontier {x in X | F x <= 1}) = 0) :
    Tendsto (fun c : Real =>
      Nat.card ({x in X | F x <= c} inter L : Set E) / (c : Real))
        atTop (𝓝 (volume.real {x in X | F x <= 1} / covolume L)) := by
  let b := Module.Free.chooseBasis Int L
  convert! tendsto_card_le_div'' b hX ?_ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b h₃.nullMeasurableSet]; rw [ENNReal.toReal_div]; rw [ENNReal.toReal_ofReal (covolume_pos L volume).le]
· have : Nontrivial L := nontrivial_of_finrank_pos (ZLattice.rank Real L).symm ▸ finrank_pos
    infer_instance
  · rwa [← finrank_eq_card_chooseBasisIndex, ZLattice.rank Real L]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume', h₄, ENNReal.zero_div]
    exact NullMeasurableSet.of_null h₄

end InnerProductSpace

end covolume

end ZLattice
