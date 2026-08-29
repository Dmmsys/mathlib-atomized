/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Lebesgue measure on `ℂ`

In this file, we consider the Lebesgue measure on `ℂ` defined as the push-forward of the volume
on `ℝ²` under the natural isomorphism and prove that it is equal to the measure `volume` of `ℂ`
coming from its `InnerProductSpace` structure over `ℝ`. For that, we consider the two frequently
used ways to represent `ℝ²` in `mathlib`: `ℝ × ℝ` and `Fin 2 → ℝ`, define measurable equivalences
(`MeasurableEquiv`) to both types and prove that both of them are volume preserving (in the sense
of `MeasureTheory.measurePreserving`).
-/

@[expose] public section

open MeasureTheory Module

noncomputable section

namespace Complex

/--
Definition of `measurableEquivPi` / `measurableEquivPi` 的定义

English:
definition measurableEquivPi
  signature: : Complex ≃ᵐ (Fin 2 -> Real)
  body: basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

@[simp]

中文:
定义 measurableEquivPi
  签名: : Complex ≃ᵐ (Fin 2 -> 实数)
  定义体: basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

@[simp]

Depends on / 依赖: basisOneI, basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv, equivFun, toContinuousLinearEquiv, toHomeomorph, toMeasurableEquiv
-/
def measurableEquivPi : Complex ≃ᵐ (Fin 2 -> Real) :=
  basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

@[simp]
/--
theorem `measurableEquivPi_apply` / 定理 `measurableEquivPi_apply`

English:
theorem measurableEquivPi_apply
  given: (a : Complex)
  proof: rfl

@[simp]

中文:
定理 measurableEquivPi_apply
  条件: (a : Complex)
  证明: rfl

@[simp]
-/
theorem measurableEquivPi_apply (a : Complex) :
    measurableEquivPi a = ![a.re, a.im] := rfl

@[simp]
/--
theorem `measurableEquivPi_symm_apply` / 定理 `measurableEquivPi_symm_apply`

English:
theorem measurableEquivPi_symm_apply
  given: (p : (Fin 2) -> Real)
  proof: rfl

中文:
定理 measurableEquivPi_symm_apply
  条件: (p : (Fin 2) -> 实数)
  证明: rfl
-/
theorem measurableEquivPi_symm_apply (p : (Fin 2) -> Real) :
    measurableEquivPi.symm p = (p 0) + (p 1) * I := rfl

/--
Definition of `measurableEquivRealProd` / `measurableEquivRealProd` 的定义

English:
definition measurableEquivRealProd
  signature: : Complex ≃ᵐ Real × Real
  body: equivRealProdCLM.toHomeomorph.toMeasurableEquiv

@[simp]

中文:
定义 measurableEquivRealProd
  签名: : Complex ≃ᵐ 实数 × 实数
  定义体: equivRealProdCLM.toHomeomorph.toMeasurableEquiv

@[simp]

Depends on / 依赖: equivRealProdCLM, equivRealProdCLM.toHomeomorph.toMeasurableEquiv, toHomeomorph, toMeasurableEquiv
-/
def measurableEquivRealProd : Complex ≃ᵐ Real × Real :=
  equivRealProdCLM.toHomeomorph.toMeasurableEquiv

@[simp]
/--
theorem `measurableEquivRealProd_apply` / 定理 `measurableEquivRealProd_apply`

English:
theorem measurableEquivRealProd_apply
  given: (a : Complex)
  statement: measurableEquivRealProd a = (a.re, a.im)
  proof: rfl

@[simp]

中文:
定理 measurableEquivRealProd_apply
  条件: (a : Complex)
  结论: measurableEquiv实数Prod a = (a.re, a.im)
  证明: rfl

@[simp]
-/
theorem measurableEquivRealProd_apply (a : Complex) : measurableEquivRealProd a = (a.re, a.im) := rfl

@[simp]
/--
theorem `measurableEquivRealProd_symm_apply` / 定理 `measurableEquivRealProd_symm_apply`

English:
theorem measurableEquivRealProd_symm_apply
  given: (p : Real × Real)
  proof: rfl

中文:
定理 measurableEquivRealProd_symm_apply
  条件: (p : 实数 × 实数)
  证明: rfl
-/
theorem measurableEquivRealProd_symm_apply (p : Real × Real) :
    measurableEquivRealProd.symm p = { re := p.1, im := p.2 } := rfl

/--
theorem `volume_preserving_equiv_pi` / 定理 `volume_preserving_equiv_pi`

English:
theorem volume_preserving_equiv_pi
  statement: MeasurePreserving measurableEquivPi
  proof: by
  convert! (measurableEquivPi.symm.measurable.measurePreserving volume).symm
  rw [← addHaarMeasure_eq_volume_pi]; rw [← Basis.parallelepiped_basisFun]; rw [← Basis.addHaar]; rw [measurableEquivPi]; rw [Homeomorph.toMeasurableEquiv_symm_coe]; rw [ContinuousLinearEquiv.coe_symm_toHomeomorph]; rw [

中文:
定理 volume_preserving_equiv_pi
  结论: MeasurePreserving measurableEquivPi
  证明: by
  convert! (measurableEquivPi.symm.measurable.measurePreserving volume).symm
  rw [← addHaarMeasure_eq_volume_pi]; rw [← Basis.parallelepiped_basisFun]; rw [← Basis.addHaar]; rw [measurableEquivPi]; rw [Homeomorph.toMeasurableEquiv_symm_coe]; rw [ContinuousLinearEquiv.coe_symm_toHomeomorph]; rw [

Depends on / 依赖: Basis.addHaar, Basis.addHaar_eq_iff, Basis.map_addHaar, Basis.parallelepiped_basisFun, Complex.orthonormalBasisOneI.volume_parallelepiped, ContinuousLinearEquiv, ContinuousLinearEquiv.coe_symm_toHomeomorph, Homeomorph, Homeomorph.toMeasurableEquiv_symm_coe, addHaar, addHaarMeasure_eq_volume_pi, addHaar_eq_iff, coe_symm_toHomeomorph, convert, eq_comm, map_addHaar, measurable, measurableEquivPi, measurableEquivPi.symm.measurable.measurePreserving, measurePreserving
-/
theorem volume_preserving_equiv_pi : MeasurePreserving measurableEquivPi := by
  convert! (measurableEquivPi.symm.measurable.measurePreserving volume).symm
  rw [← addHaarMeasure_eq_volume_pi]; rw [← Basis.parallelepiped_basisFun]; rw [← Basis.addHaar]; rw [measurableEquivPi]; rw [Homeomorph.toMeasurableEquiv_symm_coe]; rw [ContinuousLinearEquiv.coe_symm_toHomeomorph]; rw [Basis.map_addHaar]; rw [eq_comm]
  exact (Basis.addHaar_eq_iff _ _).mpr Complex.orthonormalBasisOneI.volume_parallelepiped

/--
theorem `volume_preserving_equiv_real_prod` / 定理 `volume_preserving_equiv_real_prod`

English:
theorem volume_preserving_equiv_real_prod
  statement: MeasurePreserving measurableEquivRealProd
  proof: (volume_preserving_finTwoArrow Real).comp volume_preserving_equiv_pi

中文:
定理 volume_preserving_equiv_real_prod
  结论: MeasurePreserving measurableEquiv实数Prod
  证明: (volume_preserving_finTwoArrow Real).comp volume_preserving_equiv_pi

Depends on / 依赖: volume_preserving_equiv_pi, volume_preserving_finTwoArrow
-/
theorem volume_preserving_equiv_real_prod : MeasurePreserving measurableEquivRealProd :=
  (volume_preserving_finTwoArrow Real).comp volume_preserving_equiv_pi

end Complex
