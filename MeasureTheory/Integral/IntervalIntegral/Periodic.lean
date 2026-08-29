/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Quotient
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Integrals of periodic functions

In this file we prove that the half-open interval `Ioc t (t + T)` in `ℝ` is a fundamental domain of
the action of the subgroup `ℤ ∙ T` on `ℝ`.

A consequence is `AddCircle.measurePreserving_mk`: the covering map from `ℝ` to the "additive
circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving, with respect to the restriction of Lebesgue measure to
`Ioc t (t + T)` (upstairs) and with respect to Haar measure (downstairs).

Another consequence (`Function.Periodic.intervalIntegral_add_eq` and related declarations) is that
`∫ x in t..t + T, f x = ∫ x in s..s + T, f x` for any (not necessarily measurable) function with
period `T`.
-/

@[expose] public section

open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace AddSubgroup intervalIntegral

open scoped MeasureTheory NNReal ENNReal

/-!
## Measures and integrability on ℝ and on the circle
-/

@[fun_prop]
/--
theorem `AddCircle.measurable_mk'` / 定理 `AddCircle.measurable_mk'`

English:
theorem AddCircle.measurable_mk'
  given: {a : Real}
  proof: Continuous.measurable AddCircle.continuous_mk' a

中文:
定理 AddCircle.measurable_mk'
  条件: {a : 实数}
  证明: Continuous.measurable AddCircle.continuous_mk' a
-/
protected theorem AddCircle.measurable_mk' {a : Real} :
    Measurable (β := AddCircle a) ((↑) : Real -> AddCircle a) :=
Continuous.measurable AddCircle.continuous_mk' a

/--
theorem `isAddFundamentalDomain_Ioc` / 定理 `isAddFundamentalDomain_Ioc`

English:
theorem isAddFundamentalDomain_Ioc
  statement: {T : Real} (hT : 0 < T) (t : Real)
  proof: by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : Int => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : Int => n • T) (zsmul_left_strictMono hT).injective).bijective
  refine this.existsUnique_iff.2 ?_
  simpa o

中文:
定理 isAddFundamentalDomain_Ioc
  结论: {T : 实数} (hT : 0 < T) (t : 实数)
  证明: by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : Int => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : Int => n • T) (zsmul_left_strictMono hT).injective).bijective
  refine this.existsUnique_iff.2 ?_
  simpa o

Depends on / 依赖: AddSubgroup, AddSubgroup.zmultiples, Bijective, Equiv.ofInjective, IsAddFundamentalDomain, IsAddFundamentalDomain.mk, add_comm, bijective, codRestrict, existsUnique_add_zsmul_mem_Ioc, existsUnique_iff, injective, nullMeasurableSet_Ioc, ofInjective, this.existsUnique_iff, volume_tac, zmultiples, zsmul_left_strictMono
-/
theorem isAddFundamentalDomain_Ioc {T : Real} (hT : 0 < T) (t : Real)
    (μ : Measure Real := by volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples T) (Ioc t (t + T)) μ := by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : Int => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : Int => n • T) (zsmul_left_strictMono hT).injective).bijective
  refine this.existsUnique_iff.2 ?_
  simpa only [add_comm x] using! existsUnique_add_zsmul_mem_Ioc hT x t

/--
theorem `isAddFundamentalDomain_Ioc'` / 定理 `isAddFundamentalDomain_Ioc'`

English:
theorem isAddFundamentalDomain_Ioc'
  given: {T : Real} (hT : 0 < T) (t : Real) (μ : Measure Real := by volume_tac)
  proof: by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : Int => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : Int => n • T) (zsmul_left_strictMono hT).injective).bijective
.existsUnique_iff.2 ?_ refine (AddSubgroup.eq

中文:
定理 isAddFundamentalDomain_Ioc'
  条件: {T : 实数} (hT : 0 < T) (t : 实数) (μ : Measure 实数 := by volume_tac)
  证明: by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : Int => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : Int => n • T) (zsmul_left_strictMono hT).injective).bijective
.existsUnique_iff.2 ?_ refine (AddSubgroup.eq

Depends on / 依赖: AddSubgroup, AddSubgroup.equivOp, AddSubgroup.op, AddSubgroup.zmultiples, Bijective, Equiv.ofInjective, IsAddFundamentalDomain, IsAddFundamentalDomain.mk, bijective, bijective.comp, codRestrict, equivOp, existsUnique_add_zsmul_mem_Ioc, existsUnique_iff, injective, nullMeasurableSet_Ioc, ofInjective, volume_tac, zmultiples, zsmul_left_strictMono
-/
theorem isAddFundamentalDomain_Ioc' {T : Real} (hT : 0 < T) (t : Real) (μ : Measure Real := by volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) (Ioc t (t + T)) μ := by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : Int => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : Int => n • T) (zsmul_left_strictMono hT).injective).bijective
.existsUnique_iff.2 ?_ refine (AddSubgroup.equivOp _).bijective.comp this
  simpa using! existsUnique_add_zsmul_mem_Ioc hT x t

namespace AddCircle

variable (T : Real) [hT : Fact (0 < T)]

/--
Instance `measureSpace` / 实例 `measureSpace`

English:
instance measureSpace
  signature: : MeasureSpace (AddCircle T)
  body: { QuotientAddGroup.measurableSpace _ with volume := ENNReal.ofReal T • addHaarMeasure ⊤ }

@[simp]

中文:
实例 measureSpace
  签名: : MeasureSpace (AddCircle T)
  定义体: { QuotientAddGroup.measurableSpace _ with volume := ENNReal.ofReal T • addHaarMeasure ⊤ }

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, QuotientAddGroup, QuotientAddGroup.measurableSpace, addHaarMeasure, measurableSpace, ofReal, volume
-/
noncomputable instance measureSpace : MeasureSpace (AddCircle T) :=
  { QuotientAddGroup.measurableSpace _ with volume := ENNReal.ofReal T • addHaarMeasure ⊤ }

@[simp]
/--
theorem `measure_univ` / 定理 `measure_univ`

English:
theorem measure_univ
  statement: volume (Set.univ : Set (AddCircle T)) = ENNReal.ofReal T
  proof: by
  dsimp [volume]
  rw [← PositiveCompacts.coe_top]
  simp [addHaarMeasure_self (G := AddCircle T), -PositiveCompacts.coe_top]

中文:
定理 measure_univ
  结论: volume (Set.univ : Set (AddCircle T)) = ENN实数.of实数 T
  证明: by
  dsimp [volume]
  rw [← PositiveCompacts.coe_top]
  simp [addHaarMeasure_self (G := AddCircle T), -PositiveCompacts.coe_top]
-/
protected theorem measure_univ : volume (Set.univ : Set (AddCircle T)) = ENNReal.ofReal T := by
  dsimp [volume]
  rw [← PositiveCompacts.coe_top]
  simp [addHaarMeasure_self (G := AddCircle T), -PositiveCompacts.coe_top]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddHaarMeasure (volume : Measure (AddCircle T))
  body: IsAddHaarMeasure.smul _ (by simp [hT.out]) ENNReal.ofReal_ne_top

中文:
实例 :
  签名: IsAddHaarMeasure (volume : Measure (AddCircle T))
  定义体: IsAddHaarMeasure.smul _ (by simp [hT.out]) ENNReal.ofReal_ne_top

Depends on / 依赖: ENNReal, ENNReal.ofReal_ne_top, IsAddHaarMeasure, IsAddHaarMeasure.smul, hT.out, ofReal_ne_top
-/
instance : IsAddHaarMeasure (volume : Measure (AddCircle T)) :=
  IsAddHaarMeasure.smul _ (by simp [hT.out]) ENNReal.ofReal_ne_top

/--
Instance `isFiniteMeasure` / 实例 `isFiniteMeasure`

English:
instance isFiniteMeasure
  signature: : IsFiniteMeasure (volume : Measure (AddCircle T)) where
  body: by simp

中文:
实例 isFiniteMeasure
  签名: : IsFiniteMeasure (volume : Measure (AddCircle T)) where
  定义体: by simp
-/
instance isFiniteMeasure : IsFiniteMeasure (volume : Measure (AddCircle T)) where
  measure_univ_lt_top := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) Real
  body: ⟨Ioc 0 (0 + T), isAddFundamentalDomain_Ioc' Fact.out 0⟩

中文:
实例 :
  签名: HasAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) 实数
  定义体: ⟨Ioc 0 (0 + T), isAddFundamentalDomain_Ioc' Fact.out 0⟩

Depends on / 依赖: Fact.out, isAddFundamentalDomain_Ioc
-/
instance : HasAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) Real where
  ExistsIsAddFundamentalDomain := ⟨Ioc 0 (0 + T), isAddFundamentalDomain_Ioc' Fact.out 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddQuotientMeasureEqMeasurePreimage volume (volume : Measure (AddCircle T))
  body: by
  apply MeasureTheory.leftInvariantIsAddQuotientMeasureEqMeasurePreimage
  simp [(isAddFundamentalDomain_Ioc' hT.out 0).covolume_eq_volume, AddCircle.measure_univ]

中文:
实例 :
  签名: AddQuotientMeasureEqMeasurePreimage volume (volume : Measure (AddCircle T))
  定义体: by
  apply MeasureTheory.leftInvariantIsAddQuotientMeasureEqMeasurePreimage
  simp [(isAddFundamentalDomain_Ioc' hT.out 0).covolume_eq_volume, AddCircle.measure_univ]

Depends on / 依赖: AddCircle, AddCircle.measure_univ, MeasureTheory, MeasureTheory.leftInvariantIsAddQuotientMeasureEqMeasurePreimage, covolume_eq_volume, hT.out, isAddFundamentalDomain_Ioc, leftInvariantIsAddQuotientMeasureEqMeasurePreimage, measure_univ
-/
instance : AddQuotientMeasureEqMeasurePreimage volume (volume : Measure (AddCircle T)) := by
  apply MeasureTheory.leftInvariantIsAddQuotientMeasureEqMeasurePreimage
  simp [(isAddFundamentalDomain_Ioc' hT.out 0).covolume_eq_volume, AddCircle.measure_univ]

/--
theorem `measurePreserving_mk` / 定理 `measurePreserving_mk`

English:
theorem measurePreserving_mk
  given: (t : Real)
  proof: measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage
    volume (𝓕 := Ioc t (t + T)) (isAddFundamentalDomain_Ioc' hT.out _) _

中文:
定理 measurePreserving_mk
  条件: (t : 实数)
  证明: measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage
    volume (𝓕 := Ioc t (t + T)) (isAddFundamentalDomain_Ioc' hT.out _) _
-/
protected theorem measurePreserving_mk (t : Real) :
    MeasurePreserving (β := AddCircle T) ((↑) : Real -> AddCircle T)
      (volume.restrict (Ioc t (t + T))) :=
  measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage
    volume (𝓕 := Ioc t (t + T)) (isAddFundamentalDomain_Ioc' hT.out _) _

/--
lemma `add_projection_respects_measure` / 引理 `add_projection_respects_measure`

English:
lemma add_projection_respects_measure
  given: (t : Real) {U : Set (AddCircle T)} (meas_U : MeasurableSet U)
  proof: (isAddFundamentalDomain_Ioc' hT.out _).addProjection_respects_measure_apply
    (volume : Measure (AddCircle T)) meas_U

中文:
引理 add_projection_respects_measure
  条件: (t : 实数) {U : Set (AddCircle T)} (meas_U : MeasurableSet U)
  证明: (isAddFundamentalDomain_Ioc' hT.out _).addProjection_respects_measure_apply
    (volume : Measure (AddCircle T)) meas_U

Depends on / 依赖: AddCircle, Measure, addProjection_respects_measure_apply, hT.out, isAddFundamentalDomain_Ioc, meas_U, volume
-/
lemma add_projection_respects_measure (t : Real) {U : Set (AddCircle T)} (meas_U : MeasurableSet U) :
    volume U = volume (QuotientAddGroup.mk ⁻¹' U inter (Ioc t (t + T))) :=
  (isAddFundamentalDomain_Ioc' hT.out _).addProjection_respects_measure_apply
    (volume : Measure (AddCircle T)) meas_U

/--
theorem `volume_closedBall` / 定理 `volume_closedBall`

English:
theorem volume_closedBall
  given: {x : AddCircle T} (ε : Real)
  proof: by
  have hT' : |T| = T := abs_eq_self.mpr hT.out.le
  let I := Ioc (-(T / 2)) (T / 2)
  have h₁ : ε < T / 2 -> Metric.closedBall (0 : Real) ε inter I = Metric.closedBall (0 : Real) ε := by
    intro hε
    rw [inter_eq_left]; rw [Real.closedBall_eq_Icc]; rw [zero_sub]; rw [zero_add]
    rintro y ⟨h

中文:
定理 volume_closedBall
  条件: {x : AddCircle T} (ε : 实数)
  证明: by
  have hT' : |T| = T := abs_eq_self.mpr hT.out.le
  let I := Ioc (-(T / 2)) (T / 2)
  have h₁ : ε < T / 2 -> Metric.closedBall (0 : Real) ε inter I = Metric.closedBall (0 : Real) ε := by
    intro hε
    rw [inter_eq_left]; rw [Real.closedBall_eq_Icc]; rw [zero_sub]; rw [zero_add]
    rintro y ⟨h

Depends on / 依赖: AddCircle, Iff.rfl, Metric, Metric.closedBall, Real.closedBall_eq_Icc, abs_eq_self, abs_eq_self.mpr, closedBall, closedBall_eq_Icc, conv_rhs, hT.out.le, if_ctx_congr, inter_eq_left, zero_add, zero_sub
-/
theorem volume_closedBall {x : AddCircle T} (ε : Real) :
    volume (Metric.closedBall x ε) = ENNReal.ofReal (min T (2 * ε)) := by
  have hT' : |T| = T := abs_eq_self.mpr hT.out.le
  let I := Ioc (-(T / 2)) (T / 2)
  have h₁ : ε < T / 2 -> Metric.closedBall (0 : Real) ε inter I = Metric.closedBall (0 : Real) ε := by
    intro hε
    rw [inter_eq_left]; rw [Real.closedBall_eq_Icc]; rw [zero_sub]; rw [zero_add]
    rintro y ⟨hy₁, hy₂⟩; constructor <;> linarith
  have h₂ : (↑) ⁻¹' Metric.closedBall (0 : AddCircle T) ε inter I =
      if ε < T / 2 then Metric.closedBall (0 : Real) ε else I := by
    conv_rhs => rw [← if_ctx_congr (Iff.rfl : ε < T / 2 ↔ ε < T / 2) h₁ fun _ => rfl, ← hT']
    apply coe_real_preimage_closedBall_inter_eq
    simpa only [hT', Real.closedBall_eq_Icc, zero_add, zero_sub] using Ioc_subset_Icc_self
  rw [addHaar_closedBall_center]; rw [add_projection_respects_measure T (-(T / 2))
    measurableSet_closedBall]; rw [(by linarith : -(T / 2) + T = T / 2)]; rw [h₂]
  by_cases hε : ε < T / 2
  · simp [hε, min_eq_right (by linarith : 2 * ε <= T)]
  · simp [I, hε, min_eq_left (by linarith : T <= 2 * ε)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUnifLocDoublingMeasure (volume : Measure (AddCircle T))
  body: by
  refine ⟨⟨Real.toNNReal 2, Filter.Eventually.of_forall fun ε x => ?_⟩⟩
  rw [volume_closedBall]; rw [volume_closedBall]; rw [ENNReal.ofNNReal_toNNReal 2]; rw [← ENNReal.ofReal_mul zero_le_two]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_min_of_nonneg _ _ (zero_le_two : (0 : Real) <= 2)]
  exact m

中文:
实例 :
  签名: IsUnifLocDoublingMeasure (volume : Measure (AddCircle T))
  定义体: by
  refine ⟨⟨Real.toNNReal 2, Filter.Eventually.of_forall fun ε x => ?_⟩⟩
  rw [volume_closedBall]; rw [volume_closedBall]; rw [ENNReal.ofNNReal_toNNReal 2]; rw [← ENNReal.ofReal_mul zero_le_two]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_min_of_nonneg _ _ (zero_le_two : (0 : Real) <= 2)]
  exact m

Depends on / 依赖: ENNReal, ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_le_ofReal, ENNReal.ofReal_mul, Eventually, Filter, Filter.Eventually.of_forall, Real.toNNReal, hT.out, le_refl, min_le_min, mul_min_of_nonneg, ofNNReal_toNNReal, ofReal_le_ofReal, ofReal_mul, of_forall, toNNReal, volume_closedBall, zero_le_two
-/
instance : IsUnifLocDoublingMeasure (volume : Measure (AddCircle T)) := by
  refine ⟨⟨Real.toNNReal 2, Filter.Eventually.of_forall fun ε x => ?_⟩⟩
  rw [volume_closedBall]; rw [volume_closedBall]; rw [ENNReal.ofNNReal_toNNReal 2]; rw [← ENNReal.ofReal_mul zero_le_two]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_min_of_nonneg _ _ (zero_le_two : (0 : Real) <= 2)]
  exact min_le_min (by linarith [hT.out]) (le_refl _)

/--
Definition of `measurableEquivIoc` / `measurableEquivIoc` 的定义

English:
definition measurableEquivIoc
  signature: (a : Real)
  body: equivIoc T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIoc T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_

中文:
定义 measurableEquivIoc
  签名: (a : 实数)
  定义体: equivIoc T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIoc T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_

Depends on / 依赖: equivIoc
-/
noncomputable def measurableEquivIoc (a : Real) : AddCircle T ≃ᵐ Ioc a (a + T) where
  toEquiv := equivIoc T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIoc T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe

/--
Definition of `measurableEquivIco` / `measurableEquivIco` 的定义

English:
definition measurableEquivIco
  signature: (a : Real)
  body: equivIco T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIco T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_

中文:
定义 measurableEquivIco
  签名: (a : 实数)
  定义体: equivIco T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIco T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_

Depends on / 依赖: equivIco
-/
noncomputable def measurableEquivIco (a : Real) : AddCircle T ≃ᵐ Ico a (a + T) where
  toEquiv := equivIco T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIco T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe

/--
lemma `measurePreserving_equivIoc` / 引理 `measurePreserving_equivIoc`

English:
lemma measurePreserving_equivIoc
  given: {a : Real}
  proof: by
  have h := (measurableEquivIoc T a).measurable
  refine ⟨h, ?_⟩
  ext s hs
  rw [comap_apply _ Subtype.val_injective (fun _ => measurableSet_Ioc.subtype_image) _ hs]; rw [map_apply (by measurability) hs]; rw [add_projection_respects_measure T a (by exact h hs)]
  congr!
  ext x
  simp only [mem_

中文:
引理 measurePreserving_equivIoc
  条件: {a : 实数}
  证明: by
  have h := (measurableEquivIoc T a).measurable
  refine ⟨h, ?_⟩
  ext s hs
  rw [comap_apply _ Subtype.val_injective (fun _ => measurableSet_Ioc.subtype_image) _ hs]; rw [map_apply (by measurability) hs]; rw [add_projection_respects_measure T a (by exact h hs)]
  congr!
  ext x
  simp only [mem_

Depends on / 依赖: Subtype, Subtype.exists, Subtype.val_injective, add_projection_respects_measure, and_comm, comap_apply, equivIoc_coe_eq, exists_and_right, exists_eq_right, exists_prop, map_apply, measurability, measurable, measurableEquivIoc, measurableSet_Ioc, measurableSet_Ioc.subtype_image, mem_image, mem_inter_iff, mem_preimage, subtype_image
-/
lemma measurePreserving_equivIoc {a : Real} :
    MeasurePreserving (equivIoc T a) volume (Measure.comap Subtype.val volume) := by
  have h := (measurableEquivIoc T a).measurable
  refine ⟨h, ?_⟩
  ext s hs
  rw [comap_apply _ Subtype.val_injective (fun _ => measurableSet_Ioc.subtype_image) _ hs]; rw [map_apply (by measurability) hs]; rw [add_projection_respects_measure T a (by exact h hs)]
  congr!
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right]
  rw [and_comm]; rw [← exists_prop]
  congr! with hx
  rw [equivIoc_coe_eq hx]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] Subtype.measureSpace in
/--
theorem `lintegral_preimage` / 定理 `lintegral_preimage`

English:
theorem lintegral_preimage
  given: (t : Real) (f : AddCircle T -> Real>=0∞)
  proof: by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := lintegral_map_equiv (μ := volume) f (measurableEquivIoc T t).symm
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  r

中文:
定理 lintegral_preimage
  条件: (t : 实数) (f : AddCircle T -> 实数>=0∞)
  证明: by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := lintegral_map_equiv (μ := volume) f (measurableEquivIoc T t).symm
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  r
-/
protected theorem lintegral_preimage (t : Real) (f : AddCircle T -> Real>=0∞) :
    (∫⁻ a in Ioc t (t + T), f a) = ∫⁻ b : AddCircle T, f b := by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := lintegral_map_equiv (μ := volume) f (measurableEquivIoc T t).symm
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  rw [← (AddCircle.measurePreserving_mk T t).map_eq]
  convert! this.symm using 1
  · rw [← map_comap_subtype_coe m _]
    exact MeasurableEmbedding.lintegral_map (MeasurableEmbedding.subtype_coe m) _
  · congr 1
    have : ((↑) : Ioc t (t + T) -> AddCircle T) = ((↑) : Real -> AddCircle T) ∘ ((↑) : _ -> Real) := by
      ext1 x; rfl
    simp_rw [this]
    rw [← map_map AddCircle.measurable_mk' measurable_subtype_coe]; rw [← map_comap_subtype_coe m]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] Subtype.measureSpace in
/--
theorem `integral_preimage` / 定理 `integral_preimage`

English:
theorem integral_preimage
  given: (t : Real) (f : AddCircle T -> E)
  proof: by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := integral_map_equiv (μ := volume) (measurableEquivIoc T t).symm f
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  rw

中文:
定理 integral_preimage
  条件: (t : 实数) (f : AddCircle T -> E)
  证明: by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := integral_map_equiv (μ := volume) (measurableEquivIoc T t).symm f
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  rw
-/
protected theorem integral_preimage (t : Real) (f : AddCircle T -> E) :
    (∫ a in Ioc t (t + T), f a) = ∫ b : AddCircle T, f b := by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := integral_map_equiv (μ := volume) (measurableEquivIoc T t).symm f
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  rw [← (AddCircle.measurePreserving_mk T t).map_eq]; rw [← integral_subtype m]; rw [← this]
  have : ((↑) : Ioc t (t + T) -> AddCircle T) = ((↑) : Real -> AddCircle T) ∘ ((↑) : _ -> Real) := by
    ext1 x; rfl
  simp_rw [this]
  rw [← map_map AddCircle.measurable_mk' measurable_subtype_coe]; rw [← map_comap_subtype_coe m]
  rfl

/--
theorem `intervalIntegral_preimage` / 定理 `intervalIntegral_preimage`

English:
theorem intervalIntegral_preimage
  given: (t : Real) (f : AddCircle T -> E)
  proof: by
  rw [integral_of_le]; rw [AddCircle.integral_preimage T t f]
  linarith [hT.out]

中文:
定理 intervalIntegral_preimage
  条件: (t : 实数) (f : AddCircle T -> E)
  证明: by
  rw [integral_of_le]; rw [AddCircle.integral_preimage T t f]
  linarith [hT.out]
-/
protected theorem intervalIntegral_preimage (t : Real) (f : AddCircle T -> E) :
    ∫ a in t..t + T, f a = ∫ b : AddCircle T, f b := by
  rw [integral_of_le]; rw [AddCircle.integral_preimage T t f]
  linarith [hT.out]

/--
lemma `integral_liftIoc_eq_intervalIntegral` / 引理 `integral_liftIoc_eq_intervalIntegral`

English:
lemma integral_liftIoc_eq_intervalIntegral
  given: {t : Real} {f : Real -> E}
  proof: by
  rw [← AddCircle.intervalIntegral_preimage T t]
  apply intervalIntegral.integral_congr_ae
  refine .of_forall fun x hx => ?_
  rw [uIoc_of_le (by linarith [hT.out])] at hx
  rw [liftIoc_coe_apply hx]

中文:
引理 integral_liftIoc_eq_intervalIntegral
  条件: {t : 实数} {f : 实数 -> E}
  证明: by
  rw [← AddCircle.intervalIntegral_preimage T t]
  apply intervalIntegral.integral_congr_ae
  refine .of_forall fun x hx => ?_
  rw [uIoc_of_le (by linarith [hT.out])] at hx
  rw [liftIoc_coe_apply hx]

Depends on / 依赖: AddCircle, AddCircle.intervalIntegral_preimage, hT.out, integral_congr_ae, intervalIntegral, intervalIntegral.integral_congr_ae, intervalIntegral_preimage, liftIoc_coe_apply, of_forall, uIoc_of_le
-/
lemma integral_liftIoc_eq_intervalIntegral {t : Real} {f : Real -> E} :
    ∫ a, liftIoc T t f a = ∫ a in t..t + T, f a := by
  rw [← AddCircle.intervalIntegral_preimage T t]
  apply intervalIntegral.integral_congr_ae
  refine .of_forall fun x hx => ?_
  rw [uIoc_of_le (by linarith [hT.out])] at hx
  rw [liftIoc_coe_apply hx]

end AddCircle

/--
lemma `MeasureTheory.MemLp.memLp_liftIoc` / 引理 `MeasureTheory.MemLp.memLp_liftIoc`

English:
lemma MeasureTheory.MemLp.memLp_liftIoc
  statement: {T : Real} [hT : Fact (0 < T)] {t : Real} {f : Real -> Complex} {p : Real>=0∞}
  proof: by
  simp only [AddCircle.liftIoc, Set.domRestrict_def, Function.comp_def]
  apply hLp.comp_measurePreserving
  refine .comp (measurePreserving_subtype_coe measurableSet_Ioc) ?_
  exact AddCircle.measurePreserving_equivIoc T

中文:
引理 MeasureTheory.MemLp.memLp_liftIoc
  结论: {T : 实数} [hT : Fact (0 < T)] {t : 实数} {f : 实数 -> Complex} {p : 实数>=0∞}
  证明: by
  simp only [AddCircle.liftIoc, Set.domRestrict_def, Function.comp_def]
  apply hLp.comp_measurePreserving
  refine .comp (measurePreserving_subtype_coe measurableSet_Ioc) ?_
  exact AddCircle.measurePreserving_equivIoc T

Depends on / 依赖: AddCircle, AddCircle.liftIoc, AddCircle.measurePreserving_equivIoc, Function, Function.comp_def, Set.domRestrict_def, comp_def, comp_measurePreserving, domRestrict_def, hLp.comp_measurePreserving, liftIoc, measurableSet_Ioc, measurePreserving_equivIoc, measurePreserving_subtype_coe
-/
lemma MeasureTheory.MemLp.memLp_liftIoc {T : Real} [hT : Fact (0 < T)] {t : Real} {f : Real -> Complex} {p : Real>=0∞}
    (hLp : MemLp f p (volume.restrict (Ioc t (t + T)))) :
      MemLp (AddCircle.liftIoc T t f) p := by
  simp only [AddCircle.liftIoc, Set.domRestrict_def, Function.comp_def]
  apply hLp.comp_measurePreserving
  refine .comp (measurePreserving_subtype_coe measurableSet_Ioc) ?_
  exact AddCircle.measurePreserving_equivIoc T

namespace UnitAddCircle

/--
theorem `measure_univ` / 定理 `measure_univ`

English:
theorem measure_univ
  statement: volume (Set.univ : Set UnitAddCircle) = 1
  proof: by simp

中文:
定理 measure_univ
  结论: volume (Set.univ : Set UnitAddCircle) = 1
  证明: by simp
-/
protected theorem measure_univ : volume (Set.univ : Set UnitAddCircle) = 1 := by simp

/--
theorem `measurePreserving_mk` / 定理 `measurePreserving_mk`

English:
theorem measurePreserving_mk
  given: (t : Real)
  proof: AddCircle.measurePreserving_mk 1 t

中文:
定理 measurePreserving_mk
  条件: (t : 实数)
  证明: AddCircle.measurePreserving_mk 1 t
-/
protected theorem measurePreserving_mk (t : Real) :
    MeasurePreserving (β := UnitAddCircle) ((↑) : Real -> UnitAddCircle)
      (volume.restrict (Ioc t (t + 1))) :=
  AddCircle.measurePreserving_mk 1 t

/--
theorem `lintegral_preimage` / 定理 `lintegral_preimage`

English:
theorem lintegral_preimage
  given: (t : Real) (f : UnitAddCircle -> Real>=0∞)
  proof: AddCircle.lintegral_preimage 1 t f

中文:
定理 lintegral_preimage
  条件: (t : 实数) (f : UnitAddCircle -> 实数>=0∞)
  证明: AddCircle.lintegral_preimage 1 t f
-/
protected theorem lintegral_preimage (t : Real) (f : UnitAddCircle -> Real>=0∞) :
    (∫⁻ a in Ioc t (t + 1), f a) = ∫⁻ b : UnitAddCircle, f b :=
  AddCircle.lintegral_preimage 1 t f

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
theorem `integral_preimage` / 定理 `integral_preimage`

English:
theorem integral_preimage
  given: (t : Real) (f : UnitAddCircle -> E)
  proof: AddCircle.integral_preimage 1 t f

中文:
定理 integral_preimage
  条件: (t : 实数) (f : UnitAddCircle -> E)
  证明: AddCircle.integral_preimage 1 t f
-/
protected theorem integral_preimage (t : Real) (f : UnitAddCircle -> E) :
    (∫ a in Ioc t (t + 1), f a) = ∫ b : UnitAddCircle, f b :=
  AddCircle.integral_preimage 1 t f

/--
theorem `intervalIntegral_preimage` / 定理 `intervalIntegral_preimage`

English:
theorem intervalIntegral_preimage
  given: (t : Real) (f : UnitAddCircle -> E)
  proof: AddCircle.intervalIntegral_preimage 1 t f

中文:
定理 intervalIntegral_preimage
  条件: (t : 实数) (f : UnitAddCircle -> E)
  证明: AddCircle.intervalIntegral_preimage 1 t f
-/
protected theorem intervalIntegral_preimage (t : Real) (f : UnitAddCircle -> E) :
    ∫ a in t..t + 1, f a = ∫ b : UnitAddCircle, f b :=
  AddCircle.intervalIntegral_preimage 1 t f

end UnitAddCircle

/-!
## Interval integrability of periodic functions
-/
namespace Function

namespace Periodic

variable {E : Type*} [NormedAddCommGroup E]

variable {f : Real -> E} {T : Real}

/--
theorem `intervalIntegrable` / 定理 `intervalIntegrable`

English:
theorem intervalIntegrable
  statement: {t : Real} (h₁f : Function.Periodic f T)
  proof: by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with h | h
    · tauto
    · have hnT : 0 < -T := neg_pos.mpr h
      nth_rw 1 [(by ring : t = (t + T) + (-T))] at h₂f
      apply this h₁f.neg hnT.ne' h₂f.symm _ _ hnT
  -- Replace [a₁, a₂] by [t - n₁ * T, t + n₂ * T], where n₁ and n₂ are natur

中文:
定理 intervalIntegrable
  结论: {t : 实数} (h₁f : Function.Periodic f T)
  证明: by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with h | h
    · tauto
    · have hnT : 0 < -T := neg_pos.mpr h
      nth_rw 1 [(by ring : t = (t + T) + (-T))] at h₂f
      apply this h₁f.neg hnT.ne' h₂f.symm _ _ hnT
  -- Replace [a₁, a₂] by [t - n₁ * T, t + n₂ * T], where n₁ and n₂ are natur

Depends on / 依赖: eq_or_lt, f.neg, f.symm, hnT.ne, neg_pos, neg_pos.mpr, not_lt, nth_rw
-/
theorem intervalIntegrable {t : Real} (h₁f : Function.Periodic f T)
    (hT : T != 0) (h₂f : IntervalIntegrable f volume t (t + T)) (a₁ a₂ : Real) :
    IntervalIntegrable f volume a₁ a₂ := by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with h | h
    · tauto
    · have hnT : 0 < -T := neg_pos.mpr h
      nth_rw 1 [(by ring : t = (t + T) + (-T))] at h₂f
      apply this h₁f.neg hnT.ne' h₂f.symm _ _ hnT
  -- Replace [a₁, a₂] by [t - n₁ * T, t + n₂ * T], where n₁ and n₂ are natural numbers
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge ((t - min a₁ a₂) / T)
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge ((max a₁ a₂ - t) / T)
  have : Set.uIcc a₁ a₂ subseteq Set.uIcc (t - n₁ * T) (t + n₂ * T) := by
    rw [Set.uIcc_subset_uIcc_iff_le]
    constructor
    · calc min (t - n₁ * T) (t + n₂ * T)
      _ <= (t - n₁ * T) := by apply min_le_left
      _ <= min a₁ a₂ := by linarith [(div_le_iff₀ hT).1 hn₁]
    · calc max a₁ a₂
      _ <= t + n₂ * T := by linarith [(div_le_iff₀ hT).1 hn₂]
      _ <= max (t - n₁ * T) (t + n₂ * T) := by apply le_max_right
  apply IntervalIntegrable.mono_set _ this
  -- Suffices to show integrability over shifted periods
  let a : Nat -> Real := fun n => t + (n - n₁) * T
  rw [(by ring : t - n₁ * T = a 0)]; rw [(by simp [a] : t + n₂ * T = a (n₁ + n₂))]
  apply IntervalIntegrable.trans_iterate
  -- Show integrability over a shifted period
  intro k hk
  convert! (IntervalIntegrable.comp_sub_right h₂f ((k - n₁) * T) enorm_ne_top) using 1
  · funext x
    simpa using (h₁f.sub_int_mul_eq (k - n₁)).symm
  · simp [a, Nat.cast_add]
    ring

/--
theorem `intervalIntegrable_iff` / 定理 `intervalIntegrable_iff`

English:
theorem intervalIntegrable_iff
  given: {t₁ t₂ : Real} (hf : Periodic f T)
  proof: by
  wlog hT : T != 0
  · simp_all
  exact ⟨(hf.intervalIntegrable hT · t₂ (t₂ + T)), (hf.intervalIntegrable hT · t₁ (t₁ + T))⟩

中文:
定理 intervalIntegrable_iff
  条件: {t₁ t₂ : 实数} (hf : Periodic f T)
  证明: by
  wlog hT : T != 0
  · simp_all
  exact ⟨(hf.intervalIntegrable hT · t₂ (t₂ + T)), (hf.intervalIntegrable hT · t₁ (t₁ + T))⟩

Depends on / 依赖: hf.intervalIntegrable, intervalIntegrable
-/
theorem intervalIntegrable_iff {t₁ t₂ : Real} (hf : Periodic f T) :
    IntervalIntegrable f volume t₁ (t₁ + T) ↔ IntervalIntegrable f volume t₂ (t₂ + T) := by
  wlog hT : T != 0
  · simp_all
  exact ⟨(hf.intervalIntegrable hT · t₂ (t₂ + T)), (hf.intervalIntegrable hT · t₁ (t₁ + T))⟩

/--
theorem `intervalIntegrable₀` / 定理 `intervalIntegrable₀`

English:
theorem intervalIntegrable₀
  statement: (h₁f : Function.Periodic f T) (hT : T != 0)
  proof: by
  apply h₁f.intervalIntegrable hT (t := 0)
  simpa

中文:
定理 intervalIntegrable₀
  结论: (h₁f : Function.Periodic f T) (hT : T != 0)
  证明: by
  apply h₁f.intervalIntegrable hT (t := 0)
  simpa

Depends on / 依赖: f.intervalIntegrable, intervalIntegrable
-/
theorem intervalIntegrable₀ (h₁f : Function.Periodic f T) (hT : T != 0)
    (h₂f : IntervalIntegrable f MeasureTheory.volume 0 T) (a₁ a₂ : Real) :
    IntervalIntegrable f MeasureTheory.volume a₁ a₂ := by
  apply h₁f.intervalIntegrable hT (t := 0)
  simpa

/-!
## Interval integrals of periodic functions
-/

variable [NormedSpace Real E]

/--
theorem `intervalIntegral_add_eq` / 定理 `intervalIntegral_add_eq`

English:
theorem intervalIntegral_add_eq
  given: (hf : Periodic f T) (t s : Real)
  proof: by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with hT | hT
    · simp [hT]
    · rw [← neg_inj, ← integral_symm, ← integral_symm]
      simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
        this hf.neg (t + T) (s + T) (neg_pos.mpr hT)
  simp only [integral_of_le, hT.le, le_add_i

中文:
定理 intervalIntegral_add_eq
  条件: (hf : Periodic f T) (t s : 实数)
  证明: by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with hT | hT
    · simp [hT]
    · rw [← neg_inj, ← integral_symm, ← integral_symm]
      simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
        this hf.neg (t + T) (s + T) (neg_pos.mpr hT)
  simp only [integral_of_le, hT.le, le_add_i

Depends on / 依赖: AddSubgroup, AddSubgroup.zmultiples, IsAddFundamentalDomain, IsAddFundamentalDomain.setIntegral_eq, VAddInvariantMeasure, add_sub_cancel_right, eq_or_lt, exacts, hT.le, hf.neg, integral_of_le, integral_symm, isAddFundamenta, le_add_iff_nonneg_right, measure_preimage_add, neg_inj, neg_pos, neg_pos.mpr, not_lt, setIntegral_eq
-/
theorem intervalIntegral_add_eq (hf : Periodic f T) (t s : Real) :
    ∫ x in t..t + T, f x = ∫ x in s..s + T, f x := by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with hT | hT
    · simp [hT]
    · rw [← neg_inj, ← integral_symm, ← integral_symm]
      simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
        this hf.neg (t + T) (s + T) (neg_pos.mpr hT)
  simp only [integral_of_le, hT.le, le_add_iff_nonneg_right]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples T) Real volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s, hf.map_vadd_zmultiples]

/--
theorem `intervalIntegral_add_eq_add` / 定理 `intervalIntegral_add_eq_add`

English:
theorem intervalIntegral_add_eq_add
  statement: (hf : Periodic f T) (t s : Real)
  proof: by
  rw [hf.intervalIntegral_add_eq t s]; rw [integral_add_adjacent_intervals (h_int t s) (h_int s _)]

中文:
定理 intervalIntegral_add_eq_add
  结论: (hf : Periodic f T) (t s : 实数)
  证明: by
  rw [hf.intervalIntegral_add_eq t s]; rw [integral_add_adjacent_intervals (h_int t s) (h_int s _)]

Depends on / 依赖: h_int, hf.intervalIntegral_add_eq, integral_add_adjacent_intervals, intervalIntegral_add_eq
-/
theorem intervalIntegral_add_eq_add (hf : Periodic f T) (t s : Real)
    (h_int : forall t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..s + T, f x = (∫ x in t..s, f x) + ∫ x in t..t + T, f x := by
  rw [hf.intervalIntegral_add_eq t s]; rw [integral_add_adjacent_intervals (h_int t s) (h_int s _)]

/--
theorem `intervalIntegral_add_zsmul_eq` / 定理 `intervalIntegral_add_zsmul_eq`

English:
theorem intervalIntegral_add_zsmul_eq
  statement: (hf : Periodic f T) (n : Int) (t : Real)
  proof: by
  -- Reduce to the case `b = 0`
  suffices (∫ x in 0..(n • T), f x) = n • ∫ x in 0..T, f x by
    simp only [hf.intervalIntegral_add_eq t 0, (hf.zsmul n).intervalIntegral_add_eq t 0, zero_add,
      this]
  -- First prove it for natural numbers
  have : forall m : Nat, (∫ x in 0..m • T, f x) = m 

中文:
定理 intervalIntegral_add_zsmul_eq
  结论: (hf : Periodic f T) (n : 整数) (t : 实数)
  证明: by
  -- Reduce to the case `b = 0`
  suffices (∫ x in 0..(n • T), f x) = n • ∫ x in 0..T, f x by
    simp only [hf.intervalIntegral_add_eq t 0, (hf.zsmul n).intervalIntegral_add_eq t 0, zero_add,
      this]
  -- First prove it for natural numbers
  have : forall m : Nat, (∫ x in 0..m • T, f x) = m 
-/
theorem intervalIntegral_add_zsmul_eq (hf : Periodic f T) (n : Int) (t : Real)
    (h_int : forall t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..t + n • T, f x = n • ∫ x in t..t + T, f x := by
  -- Reduce to the case `b = 0`
  suffices (∫ x in 0..(n • T), f x) = n • ∫ x in 0..T, f x by
    simp only [hf.intervalIntegral_add_eq t 0, (hf.zsmul n).intervalIntegral_add_eq t 0, zero_add,
      this]
  -- First prove it for natural numbers
  have : forall m : Nat, (∫ x in 0..m • T, f x) = m • ∫ x in 0..T, f x := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [succ_nsmul, hf.intervalIntegral_add_eq_add 0 (m • T) h_int, ih, zero_add]
  -- Then prove it for all integers
  rcases n with n | n
  · simp [← this n]
  · conv_rhs => rw [negSucc_zsmul]
    have h₀ : Int.negSucc n • T + (n + 1) • T = 0 := by simp; linarith
    rw [integral_symm]; rw [← (hf.nsmul (n + 1)).funext]; rw [neg_inj]
    simp_rw [integral_comp_add_right, h₀, zero_add, this (n + 1), add_comm T,
      hf.intervalIntegral_add_eq ((n + 1) • T) 0, zero_add]

section RealValued

open Filter

variable {g : Real -> Real}
variable (hg : Periodic g T)
include hg

/--
theorem `sInf_add_zsmul_le_integral_of_pos` / 定理 `sInf_add_zsmul_le_integral_of_pos`

English:
theorem sInf_add_zsmul_le_integral_of_pos
  statement: (h_int : IntervalIntegrable g MeasureSpace.volume 0 T)
  proof: by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_rhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne']; rw [← integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε (hg.intervalIntegrable₀ h

中文:
定理 sInf_add_zsmul_le_integral_of_pos
  结论: (h_int : 整数erval整数egrable g MeasureSpace.volume 0 T)
  证明: by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_rhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne']; rw [← integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε (hg.intervalIntegrable₀ h

Depends on / 依赖: Int.fract, Int.fract_div_mul_self_add_zsmul_eq, Int.fract_div_mul_self_mem_Ico, _int, add_le_add_iff_right, continuousOn, continuousOn.sInf_image_Icc_le, continuous_primitive, conv_rhs, fract_div_mul_self_add_zsmul_eq, fract_div_mul_self_mem_Ico, hT.ne, h_int, hg.intervalIntegrable, hg.intervalIntegral_add_eq, hg.intervalIntegral_add_zsmul_eq, integral_add_adjacent_intervals, intervalIntegral_add_eq, intervalIntegral_add_zsmul_eq, mem_Icc_of_Ico
-/
theorem sInf_add_zsmul_le_integral_of_pos (h_int : IntervalIntegrable g MeasureSpace.volume 0 T)
    (hT : 0 < T) (t : Real) :
    (sInf ((fun t => ∫ x in 0..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in 0..T, g x) <=
      ∫ x in 0..t, g x := by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_rhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne']; rw [← integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε (hg.intervalIntegrable₀ hT.ne' h_int)]; rw [hg.intervalIntegral_add_eq ε 0]; rw [zero_add]; rw [add_le_add_iff_right]
exact (continuous_primitive h'_int 0).continuousOn.sInf_image_Icc_le
    mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT)

/--
theorem `integral_le_sSup_add_zsmul_of_pos` / 定理 `integral_le_sSup_add_zsmul_of_pos`

English:
theorem integral_le_sSup_add_zsmul_of_pos
  statement: (h_int : IntervalIntegrable g MeasureSpace.volume 0 T)
  proof: by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_lhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne']; rw [←
      integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε h'_int]; rw [hg.int

中文:
定理 integral_le_sSup_add_zsmul_of_pos
  结论: (h_int : 整数erval整数egrable g MeasureSpace.volume 0 T)
  证明: by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_lhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne']; rw [←
      integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε h'_int]; rw [hg.int

Depends on / 依赖: Int.fract, Int.fract_div_mul_self_add_zsmul_eq, Int.fract_div_mul_self_mem_Ico, _int, add_le_add_iff_right, continuousOn, continuousOn.le_sSup_image_Icc, continuous_primitive, conv_lhs, fract_div_mul_self_add_zsmul_eq, fract_div_mul_self_mem_Ico, hT.ne, h_int, hg.intervalIntegrable, hg.intervalIntegral_add_eq, hg.intervalIntegral_add_zsmul_eq, integral_add_adjacent_intervals, intervalIntegral_add_eq, intervalIntegral_add_zsmul_eq, le_sSup_image_Icc
-/
theorem integral_le_sSup_add_zsmul_of_pos (h_int : IntervalIntegrable g MeasureSpace.volume 0 T)
    (hT : 0 < T) (t : Real) :
    (∫ x in 0..t, g x) <=
      sSup ((fun t => ∫ x in 0..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in 0..T, g x := by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_lhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne']; rw [←
      integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε h'_int]; rw [hg.intervalIntegral_add_eq ε 0]; rw [zero_add]; rw [add_le_add_iff_right]
  exact (continuous_primitive h'_int 0).continuousOn.le_sSup_image_Icc
    (mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT))

/--
theorem `tendsto_atTop_intervalIntegral_of_pos` / 定理 `tendsto_atTop_intervalIntegral_of_pos`

English:
theorem tendsto_atTop_intervalIntegral_of_pos
  given: (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T)
  proof: by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atTop_mono (hg.sInf_add_zsmul_le_integral_of_pos h_int hT)
  apply atTop.tendsto_atTop_add_const_left (sInf <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atTop_zsmul_const h₀
  exact tendsto_floor_atTop.com

中文:
定理 tendsto_atTop_intervalIntegral_of_pos
  条件: (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T)
  证明: by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atTop_mono (hg.sInf_add_zsmul_le_integral_of_pos h_int hT)
  apply atTop.tendsto_atTop_add_const_left (sInf <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atTop_zsmul_const h₀
  exact tendsto_floor_atTop.com

Depends on / 依赖: Tendsto, Tendsto.atTop_zsmul_const, atTop.tendsto_atTop_add_const_left, atTop_mul_const, atTop_zsmul_const, h_int, hg.sInf_add_zsmul_le_integral_of_pos, intervalIntegrable_of_integral_ne_zero, inv_pos, inv_pos.mpr, sInf_add_zsmul_le_integral_of_pos, tendsto_atTop_add_const_left, tendsto_atTop_mono, tendsto_floor_atTop, tendsto_floor_atTop.comp, tendsto_id, tendsto_id.atTop_mul_const
-/
theorem tendsto_atTop_intervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atTop atTop := by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atTop_mono (hg.sInf_add_zsmul_le_integral_of_pos h_int hT)
  apply atTop.tendsto_atTop_add_const_left (sInf <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atTop_zsmul_const h₀
  exact tendsto_floor_atTop.comp (tendsto_id.atTop_mul_const (inv_pos.mpr hT))

/--
theorem `tendsto_atBot_intervalIntegral_of_pos` / 定理 `tendsto_atBot_intervalIntegral_of_pos`

English:
theorem tendsto_atBot_intervalIntegral_of_pos
  given: (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T)
  proof: by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atBot_mono (hg.integral_le_sSup_add_zsmul_of_pos h_int hT)
  apply atBot.tendsto_atBot_add_const_left (sSup <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atBot_zsmul_const h₀
  exact tendsto_floor_atBot.com

中文:
定理 tendsto_atBot_intervalIntegral_of_pos
  条件: (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T)
  证明: by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atBot_mono (hg.integral_le_sSup_add_zsmul_of_pos h_int hT)
  apply atBot.tendsto_atBot_add_const_left (sSup <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atBot_zsmul_const h₀
  exact tendsto_floor_atBot.com

Depends on / 依赖: Tendsto, Tendsto.atBot_zsmul_const, atBot.tendsto_atBot_add_const_left, atBot_mul_const, atBot_zsmul_const, h_int, hg.integral_le_sSup_add_zsmul_of_pos, integral_le_sSup_add_zsmul_of_pos, intervalIntegrable_of_integral_ne_zero, inv_pos, inv_pos.mpr, tendsto_atBot_add_const_left, tendsto_atBot_mono, tendsto_floor_atBot, tendsto_floor_atBot.comp, tendsto_id, tendsto_id.atBot_mul_const
-/
theorem tendsto_atBot_intervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atBot atBot := by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atBot_mono (hg.integral_le_sSup_add_zsmul_of_pos h_int hT)
  apply atBot.tendsto_atBot_add_const_left (sSup <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atBot_zsmul_const h₀
  exact tendsto_floor_atBot.comp (tendsto_id.atBot_mul_const (inv_pos.mpr hT))

/--
theorem `tendsto_atTop_intervalIntegral_of_pos'` / 定理 `tendsto_atTop_intervalIntegral_of_pos'`

English:
theorem tendsto_atTop_intervalIntegral_of_pos'
  proof: hg.tendsto_atTop_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

中文:
定理 tendsto_atTop_intervalIntegral_of_pos'
  证明: hg.tendsto_atTop_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

Depends on / 依赖: h_int, hg.tendsto_atTop_intervalIntegral_of_pos, intervalIntegral_pos_of_pos, tendsto_atTop_intervalIntegral_of_pos
-/
theorem tendsto_atTop_intervalIntegral_of_pos'
    (h_int : IntervalIntegrable g MeasureSpace.volume 0 T) (h₀ : forall x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atTop atTop :=
  hg.tendsto_atTop_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

/--
theorem `tendsto_atBot_intervalIntegral_of_pos'` / 定理 `tendsto_atBot_intervalIntegral_of_pos'`

English:
theorem tendsto_atBot_intervalIntegral_of_pos'
  proof: by
  exact hg.tendsto_atBot_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

中文:
定理 tendsto_atBot_intervalIntegral_of_pos'
  证明: by
  exact hg.tendsto_atBot_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

Depends on / 依赖: h_int, hg.tendsto_atBot_intervalIntegral_of_pos, intervalIntegral_pos_of_pos, tendsto_atBot_intervalIntegral_of_pos
-/
theorem tendsto_atBot_intervalIntegral_of_pos'
    (h_int : IntervalIntegrable g MeasureSpace.volume 0 T) (h₀ : forall x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atBot atBot := by
  exact hg.tendsto_atBot_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

end RealValued

end Periodic

end Function
