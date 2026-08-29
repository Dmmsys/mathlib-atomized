/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`MeasureTheory.addHaarMeasure_eq_volume` and `MeasureTheory.addHaarMeasure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite-dimensional real vector space:
* `map_linearMap_addHaar_eq_smul_addHaar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.
* `addHaar_preimage_linearMap` : when `f` is a linear map with nonzero determinant, the measure
  of `f ⁻¹' s` is the measure of `s` multiplied by the absolute value of the inverse of the
  determinant of `f`.
* `addHaar_image_linearMap` : when `f` is a linear map, the measure of `f '' s` is the
  measure of `s` multiplied by the absolute value of the determinant of `f`.
* `addHaar_submodule` : a strict submodule has measure `0`.
* `addHaar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `addHaar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `addHaar_closedBall`: the measure of `closedBall x r` is `r ^ dim * μ (ball 0 1)`.
* `addHaar_sphere`: spheres have zero measure.

This makes it possible to associate a Lebesgue measure to an `n`-alternating map in dimension `n`.
This measure is called `AlternatingMap.measure`. Its main property is
`ω.measure_parallelepiped v`, stating that the associated measure of the parallelepiped spanned
by vectors `v₁, ..., vₙ` is given by `|ω v|`.

We also show that a Lebesgue density point `x` of a set `s` (with respect to closed balls) has
density one for the rescaled copies `{x} + r • t` of a given set `t` with positive measure, in
`tendsto_addHaar_inter_smul_one_of_density_one`. In particular, `s` intersects `{x} + r • t` for
small `r`, see `eventually_nonempty_inter_smul_of_density_one`.

Statements on integrals of functions with respect to an additive Haar measure can be found in
`MeasureTheory.Measure.Haar.NormedSpace`.
-/

@[expose] public section

assert_not_exists MeasureTheory.integral

open TopologicalSpace Set Filter Metric Bornology

open scoped ENNReal Pointwise Topology NNReal

/--
Definition of `TopologicalSpace.PositiveCompacts.Icc01` / `TopologicalSpace.PositiveCompacts.Icc01` 的定义

English:
definition TopologicalSpace.PositiveCompacts.Icc01
  signature: : PositiveCompacts Real where
  body: Icc 0 1
  isCompact' := isCompact_Icc
  interior_nonempty' := by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]

universe u

中文:
定义 TopologicalSpace.PositiveCompacts.Icc01
  签名: : PositiveCompacts 实数 where
  定义体: Icc 0 1
  isCompact' := isCompact_Icc
  interior_nonempty' := by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]

universe u
-/
def TopologicalSpace.PositiveCompacts.Icc01 : PositiveCompacts Real where
  carrier := Icc 0 1
  isCompact' := isCompact_Icc
  interior_nonempty' := by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]

universe u

/--
Definition of `TopologicalSpace.PositiveCompacts.piIcc01` / `TopologicalSpace.PositiveCompacts.piIcc01` 的定义

English:
definition TopologicalSpace.PositiveCompacts.piIcc01
  signature: (ι : Type*) [Finite ι]
  body: pi univ fun _ => Icc 0 1
  isCompact' := isCompact_univ_pi fun _ => isCompact_Icc
  interior_nonempty' := by
    simp only [interior_pi_set, Set.toFinite, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo,
      imp_true_iff, zero_lt_one]

中文:
定义 TopologicalSpace.PositiveCompacts.piIcc01
  签名: (ι : 类型) [Finite ι]
  定义体: pi univ fun _ => Icc 0 1
  isCompact' := isCompact_univ_pi fun _ => isCompact_Icc
  interior_nonempty' := by
    simp only [interior_pi_set, Set.toFinite, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo,
      imp_true_iff, zero_lt_one]
-/
def TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type*) [Finite ι] :
    PositiveCompacts (ι -> Real) where
  carrier := pi univ fun _ => Icc 0 1
  isCompact' := isCompact_univ_pi fun _ => isCompact_Icc
  interior_nonempty' := by
    simp only [interior_pi_set, Set.toFinite, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo,
      imp_true_iff, zero_lt_one]

namespace Module.Basis

/--
theorem `parallelepiped_basisFun` / 定理 `parallelepiped_basisFun`

English:
theorem parallelepiped_basisFun
  given: (ι : Type*) [Fintype ι]
  proof: SetLike.coe_injective by
    refine Eq.trans ?_ ((uIcc_of_le ?_).trans (Set.pi_univ_Icc _ _).symm)
    · classical convert! parallelepiped_single (ι := ι) 1
    · exact zero_le_one

中文:
定理 parallelepiped_basisFun
  条件: (ι : 类型) [Fintype ι]
  证明: SetLike.coe_injective by
    refine Eq.trans ?_ ((uIcc_of_le ?_).trans (Set.pi_univ_Icc _ _).symm)
    · classical convert! parallelepiped_single (ι := ι) 1
    · exact zero_le_one

Depends on / 依赖: Eq.trans, Set.pi_univ_Icc, SetLike, SetLike.coe_injective, classical, coe_injective, convert, parallelepiped_single, pi_univ_Icc, uIcc_of_le, zero_le_one
-/
theorem parallelepiped_basisFun (ι : Type*) [Fintype ι] :
    (Pi.basisFun Real ι).parallelepiped = TopologicalSpace.PositiveCompacts.piIcc01 ι :=
SetLike.coe_injective by
    refine Eq.trans ?_ ((uIcc_of_le ?_).trans (Set.pi_univ_Icc _ _).symm)
    · classical convert! parallelepiped_single (ι := ι) 1
    · exact zero_le_one

/--
theorem `parallelepiped_eq_map` / 定理 `parallelepiped_eq_map`

English:
theorem parallelepiped_eq_map
  statement: {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
  proof: by
  classical
  rw [← Basis.parallelepiped_basisFun]; rw [← Basis.parallelepiped_map]
  congr with x
  simp [Pi.single_apply]

中文:
定理 parallelepiped_eq_map
  结论: {ι E : 类型} [Fintype ι] [NormedAddCommGroup E]
  证明: by
  classical
  rw [← Basis.parallelepiped_basisFun]; rw [← Basis.parallelepiped_map]
  congr with x
  simp [Pi.single_apply]

Depends on / 依赖: Basis.parallelepiped_basisFun, Basis.parallelepiped_map, Pi.single_apply, classical, parallelepiped_basisFun, parallelepiped_map, single_apply
-/
theorem parallelepiped_eq_map {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace Real E] (b : Basis ι Real E) :
    b.parallelepiped = (PositiveCompacts.piIcc01 ι).map b.equivFun.symm
      b.equivFunL.symm.continuous b.equivFunL.symm.isOpenMap := by
  classical
  rw [← Basis.parallelepiped_basisFun]; rw [← Basis.parallelepiped_map]
  congr with x
  simp [Pi.single_apply]

open MeasureTheory MeasureTheory.Measure

/--
theorem `map_addHaar` / 定理 `map_addHaar`

English:
theorem map_addHaar
  statement: {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedAddCommGroup F]
  proof: by
  rw [eq_comm]; rw [Basis.addHaar_eq_iff]; rw [Measure.map_apply f.continuous.measurable
    (PositiveCompacts.isCompact _).measurableSet]; rw [Basis.coe_parallelepiped]; rw [Basis.coe_map]; rw [← addHaar_self b]; rw [← f.toEquiv.preimage_image (_root_.parallelepiped ⇑b)]
  have := image_parallel

中文:
定理 map_addHaar
  结论: {ι E F : 类型} [Fintype ι] [NormedAddCommGroup E] [NormedAddCommGroup F]
  证明: by
  rw [eq_comm]; rw [Basis.addHaar_eq_iff]; rw [Measure.map_apply f.continuous.measurable
    (PositiveCompacts.isCompact _).measurableSet]; rw [Basis.coe_parallelepiped]; rw [Basis.coe_map]; rw [← addHaar_self b]; rw [← f.toEquiv.preimage_image (_root_.parallelepiped ⇑b)]
  have := image_parallel

Depends on / 依赖: Basis.addHaar_eq_iff, Basis.coe_map, Basis.coe_parallelepiped, Measure, Measure.map_apply, PositiveCompacts, PositiveCompacts.isCompact, _root_, _root_.parallelepiped, addHaar_eq_iff, addHaar_self, coe_map, coe_parallelepiped, continuous, eq_comm, f.continuous.measurable, f.toEquiv.preimage_image, f.toLinearMap, image_parallelepiped, isCompact
-/
theorem map_addHaar {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace Real E] [NormedSpace Real F] [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E]
    [BorelSpace F] [SecondCountableTopology F] [SigmaCompactSpace F]
    (b : Basis ι Real E) (f : E ≃L[Real] F) :
    map f b.addHaar = (b.map f.toLinearEquiv).addHaar := by
  rw [eq_comm]; rw [Basis.addHaar_eq_iff]; rw [Measure.map_apply f.continuous.measurable
    (PositiveCompacts.isCompact _).measurableSet]; rw [Basis.coe_parallelepiped]; rw [Basis.coe_map]; rw [← addHaar_self b]; rw [← f.toEquiv.preimage_image (_root_.parallelepiped ⇑b)]
  have := image_parallelepiped f.toLinearMap (⇑b : ι -> E)
  simp_all

end Module.Basis

namespace MeasureTheory

open Measure TopologicalSpace.PositiveCompacts Module

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/

/--
theorem `addHaarMeasure_eq_volume` / 定理 `addHaarMeasure_eq_volume`

English:
theorem addHaarMeasure_eq_volume
  statement: addHaarMeasure Icc01 = volume
  proof: by
  convert! (addHaarMeasure_unique volume Icc01).symm; simp [Icc01]

中文:
定理 addHaarMeasure_eq_volume
  结论: addHaarMeasure Icc01 = volume
  证明: by
  convert! (addHaarMeasure_unique volume Icc01).symm; simp [Icc01]

Depends on / 依赖: addHaarMeasure_unique, convert, volume
-/
theorem addHaarMeasure_eq_volume : addHaarMeasure Icc01 = volume := by
  convert! (addHaarMeasure_unique volume Icc01).symm; simp [Icc01]

/--
theorem `addHaarMeasure_eq_volume_pi` / 定理 `addHaarMeasure_eq_volume_pi`

English:
theorem addHaarMeasure_eq_volume_pi
  given: (ι : Type*) [Fintype ι]
  proof: by
  convert! (addHaarMeasure_unique volume (piIcc01 ι)).symm
  simp only [piIcc01, volume_pi_pi fun _ => Icc (0 : Real) 1, PositiveCompacts.coe_mk,
    Compacts.coe_mk, Finset.prod_const_one, ENNReal.ofReal_one, Real.volume_Icc, one_smul, sub_zero]

中文:
定理 addHaarMeasure_eq_volume_pi
  条件: (ι : 类型) [Fintype ι]
  证明: by
  convert! (addHaarMeasure_unique volume (piIcc01 ι)).symm
  simp only [piIcc01, volume_pi_pi fun _ => Icc (0 : Real) 1, PositiveCompacts.coe_mk,
    Compacts.coe_mk, Finset.prod_const_one, ENNReal.ofReal_one, Real.volume_Icc, one_smul, sub_zero]

Depends on / 依赖: Compacts, Compacts.coe_mk, ENNReal, ENNReal.ofReal_one, Finset, Finset.prod_const_one, PositiveCompacts, PositiveCompacts.coe_mk, Real.volume_Icc, addHaarMeasure_unique, coe_mk, convert, ofReal_one, one_smul, piIcc01, prod_const_one, sub_zero, volume, volume_Icc, volume_pi_pi
-/
theorem addHaarMeasure_eq_volume_pi (ι : Type*) [Fintype ι] :
    addHaarMeasure (piIcc01 ι) = volume := by
  convert! (addHaarMeasure_unique volume (piIcc01 ι)).symm
  simp only [piIcc01, volume_pi_pi fun _ => Icc (0 : Real) 1, PositiveCompacts.coe_mk,
    Compacts.coe_mk, Finset.prod_const_one, ENNReal.ofReal_one, Real.volume_Icc, one_smul, sub_zero]

/--
theorem `isAddHaarMeasure_volume_pi` / 定理 `isAddHaarMeasure_volume_pi`

English:
theorem isAddHaarMeasure_volume_pi
  given: (ι : Type*) [Fintype ι]
  proof: inferInstance

中文:
定理 isAddHaarMeasure_volume_pi
  条件: (ι : 类型) [Fintype ι]
  证明: inferInstance
-/
theorem isAddHaarMeasure_volume_pi (ι : Type*) [Fintype ι] :
    IsAddHaarMeasure (volume : Measure (ι -> Real)) :=
  inferInstance

namespace Measure

/-!
### Strict subspaces have zero measure
-/

open scoped Function -- required for scoped `on` notation

/--
theorem `addHaar_eq_zero_of_disjoint_translates_aux` / 定理 `addHaar_eq_zero_of_disjoint_translates_aux`

English:
theorem addHaar_eq_zero_of_disjoint_translates_aux
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  by_contra h
  apply lt_irrefl ∞
  calc
    ∞ = ∑' _ : Nat, μ s := (ENNReal.tsum_const_eq_top_of_ne_zero h).symm
    _ = ∑' n : Nat, μ ({u n} + s) := by
      congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
_ = μ (⋃ n, {u n} + s) := Eq.symm measure_iUnion hs fun 

中文:
定理 addHaar_eq_zero_of_disjoint_translates_aux
  结论: {E : 类型} [NormedAddCommGroup E]
  证明: by
  by_contra h
  apply lt_irrefl ∞
  calc
    ∞ = ∑' _ : Nat, μ s := (ENNReal.tsum_const_eq_top_of_ne_zero h).symm
    _ = ∑' n : Nat, μ ({u n} + s) := by
      congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
_ = μ (⋃ n, {u n} + s) := Eq.symm measure_iUnion hs fun 

Depends on / 依赖: ENNReal, ENNReal.tsum_const_eq_top_of_ne_zero, Eq.symm, const_add, hu.add, iUnion_add, iUnion_singleton_eq_range, image_add_left, lt_irrefl, measurable_id, measurable_id.const_add, measure_iUnion, measure_lt_top, measure_preimage_add, singleton_add, tsum_const_eq_top_of_ne_zero
-/
theorem addHaar_eq_zero_of_disjoint_translates_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : Nat -> E) (sb : IsBounded s) (hu : IsBounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  by_contra h
  apply lt_irrefl ∞
  calc
    ∞ = ∑' _ : Nat, μ s := (ENNReal.tsum_const_eq_top_of_ne_zero h).symm
    _ = ∑' n : Nat, μ ({u n} + s) := by
      congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
_ = μ (⋃ n, {u n} + s) := Eq.symm measure_iUnion hs fun n => by
      simpa only [image_add_left, singleton_add] using! measurable_id.const_add _ h's
    _ = μ (range u + s) := by rw [← iUnion_add, iUnion_singleton_eq_range]
    _ < ∞ := (hu.add sb).measure_lt_top

/--
theorem `addHaar_eq_zero_of_disjoint_translates` / 定理 `addHaar_eq_zero_of_disjoint_translates`

English:
theorem addHaar_eq_zero_of_disjoint_translates
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  suffices H : forall R, μ (s inter closedBall 0 R) = 0 by
    rw [← nonpos_iff_eq_zero]
    calc
      μ s <= ∑' n : Nat, μ (s inter closedBall 0 n) := by
        conv_lhs => rw [← iUnion_inter_closedBall_nat s 0]
        exact measure_iUnion_le _
      _ = 0 := by simp only [H, tsum_zero]
  int

中文:
定理 addHaar_eq_zero_of_disjoint_translates
  结论: {E : 类型} [NormedAddCommGroup E]
  证明: by
  suffices H : forall R, μ (s inter closedBall 0 R) = 0 by
    rw [← nonpos_iff_eq_zero]
    calc
      μ s <= ∑' n : Nat, μ (s inter closedBall 0 n) := by
        conv_lhs => rw [← iUnion_inter_closedBall_nat s 0]
        exact measure_iUnion_le _
      _ = 0 := by simp only [H, tsum_zero]
  int

Depends on / 依赖: Subset, Subset.rfl, addHaar_eq_zero_of_disjoint_translates_aux, add_subset_add, closedBall, conv_lhs, iUnion_inter_closedBall_nat, inter_subset_l, inter_subset_right, isBounded_closedBall, isBounded_closedBall.subset, measurableSet_closedBall, measure_iUnion_le, nonpos_iff_eq_zero, pairwise_disjoint_mono, s.inter, subset, tsum_zero
-/
theorem addHaar_eq_zero_of_disjoint_translates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : Nat -> E) (hu : IsBounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  suffices H : forall R, μ (s inter closedBall 0 R) = 0 by
    rw [← nonpos_iff_eq_zero]
    calc
      μ s <= ∑' n : Nat, μ (s inter closedBall 0 n) := by
        conv_lhs => rw [← iUnion_inter_closedBall_nat s 0]
        exact measure_iUnion_le _
      _ = 0 := by simp only [H, tsum_zero]
  intro R
  apply addHaar_eq_zero_of_disjoint_translates_aux μ u
    (isBounded_closedBall.subset inter_subset_right) hu _ (h's.inter measurableSet_closedBall)
  refine pairwise_disjoint_mono hs fun n => ?_
  exact add_subset_add Subset.rfl inter_subset_left

/--
theorem `addHaar_submodule` / 定理 `addHaar_submodule`

English:
theorem addHaar_submodule
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E]
  proof: by
  obtain ⟨x, hx⟩ : exists x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hs
  obtain ⟨c, cpos, cone⟩ : exists c : Real, 0 < c ∧ c < 1 := ⟨1 / 2, by simp, by norm_num⟩
  have A : IsBounded (range fun n : Nat => c ^ n • x) :=
    have : Tendsto (fun n : Nat 

中文:
定理 addHaar_submodule
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E] [MeasurableSpace E]
  证明: by
  obtain ⟨x, hx⟩ : exists x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hs
  obtain ⟨c, cpos, cone⟩ : exists c : Real, 0 < c ∧ c < 1 := ⟨1 / 2, by simp, by norm_num⟩
  have A : IsBounded (range fun n : Nat => c ^ n • x) :=
    have : Tendsto (fun n : Nat 

Depends on / 依赖: IsBounded, Submodule, Submodule.closed, Submodule.eq_top_iff, Tendsto, addHaar_eq_zero_of_disjoint_translates, closed, cpos.le, eq_top_iff, isBounded_range_of_tendsto, not_exists, not_forall, smul_const, tendsto_pow_atTop_nhds_zero_of_lt_one
-/
theorem addHaar_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional Real E] (μ : Measure E) [IsAddHaarMeasure μ] (s : Submodule Real E)
    (hs : s != ⊤) : μ s = 0 := by
  obtain ⟨x, hx⟩ : exists x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hs
  obtain ⟨c, cpos, cone⟩ : exists c : Real, 0 < c ∧ c < 1 := ⟨1 / 2, by simp, by norm_num⟩
  have A : IsBounded (range fun n : Nat => c ^ n • x) :=
    have : Tendsto (fun n : Nat => c ^ n • x) atTop (𝓝 ((0 : Real) • x)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one cpos.le cone).smul_const x
    isBounded_range_of_tendsto _ this
  apply addHaar_eq_zero_of_disjoint_translates μ _ A _
    (Submodule.closed_of_finiteDimensional s).measurableSet
  intro m n hmn
  simp only [Function.onFun, image_add_left, singleton_add, disjoint_left, mem_preimage,
    SetLike.mem_coe]
  intro y hym hyn
  have A : (c ^ n - c ^ m) • x in s := by
    convert! s.sub_mem hym hyn using 1
    simp only [sub_smul, neg_sub_neg, add_sub_add_right_eq_sub]
  have H : c ^ n - c ^ m != 0 := by
    simpa only [sub_eq_zero, Ne] using (pow_right_strictAnti₀ cpos cone).injective.ne hmn.symm
  have : x in s := by
    convert! s.smul_mem (c ^ n - c ^ m)⁻¹ A
    rw [smul_smul]; rw [inv_mul_cancel₀ H]; rw [one_smul]
  exact hx this

/--
theorem `addHaar_affineSubspace` / 定理 `addHaar_affineSubspace`

English:
theorem addHaar_affineSubspace
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rcases s.eq_bot_or_nonempty with (rfl | hne)
  · rw [AffineSubspace.bot_coe, measure_empty]
  rw [Ne]; rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne] at hs
  rcases hne with ⟨x, hx : x in s⟩
  simpa only [AffineSubspace.coe_direction_eq_vsub_set_right hx, vsub_eq_sub, sub_eq_add_neg

中文:
定理 addHaar_affineSubspace
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: by
  rcases s.eq_bot_or_nonempty with (rfl | hne)
  · rw [AffineSubspace.bot_coe, measure_empty]
  rw [Ne]; rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne] at hs
  rcases hne with ⟨x, hx : x in s⟩
  simpa only [AffineSubspace.coe_direction_eq_vsub_set_right hx, vsub_eq_sub, sub_eq_add_neg

Depends on / 依赖: AffineSubspace, AffineSubspace.bot_coe, AffineSubspace.coe_direction_eq_vsub_set_right, AffineSubspace.direction_eq_top_iff_of_nonempty, addHaar_submodule, bot_coe, coe_direction_eq_vsub_set_right, direction, direction_eq_top_iff_of_nonempty, eq_bot_or_nonempty, image_add_right, measure_empty, measure_preimage_add_right, neg_neg, s.direction, s.eq_bot_or_nonempty, sub_eq_add_neg, vsub_eq_sub
-/
theorem addHaar_affineSubspace {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E] (μ : Measure E) [IsAddHaarMeasure μ]
    (s : AffineSubspace Real E) (hs : s != ⊤) : μ s = 0 := by
  rcases s.eq_bot_or_nonempty with (rfl | hne)
  · rw [AffineSubspace.bot_coe, measure_empty]
  rw [Ne]; rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne] at hs
  rcases hne with ⟨x, hx : x in s⟩
  simpa only [AffineSubspace.coe_direction_eq_vsub_set_right hx, vsub_eq_sub, sub_eq_add_neg,
    image_add_right, neg_neg, measure_preimage_add_right] using addHaar_submodule μ s.direction hs


/--
theorem `map_linearMap_addHaar_pi_eq_smul_addHaar` / 定理 `map_linearMap_addHaar_pi_eq_smul_addHaar`

English:
theorem map_linearMap_addHaar_pi_eq_smul_addHaar
  statement: {ι : Type*} [Finite ι] {f : (ι -> Real) ->ₗ[Real] ι -> Real}
  proof: by
  cases nonempty_fintype ι
  /- We have already proved the result for the Lebesgue product measure, using matrices.
    We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := addHaarMeasure_unique μ (piIcc01 ι)
  rw [this]; rw [addHaarMeasure_eq_volume_pi]; rw

中文:
定理 map_linearMap_addHaar_pi_eq_smul_addHaar
  结论: {ι : 类型} [Finite ι] {f : (ι -> 实数) ->ₗ[实数] ι -> 实数}
  证明: by
  cases nonempty_fintype ι
  /- We have already proved the result for the Lebesgue product measure, using matrices.
    We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := addHaarMeasure_unique μ (piIcc01 ι)
  rw [this]; rw [addHaarMeasure_eq_volume_pi]; rw

Depends on / 依赖: nonempty_fintype
-/
theorem map_linearMap_addHaar_pi_eq_smul_addHaar {ι : Type*} [Finite ι] {f : (ι -> Real) ->ₗ[Real] ι -> Real}
    (hf : LinearMap.det f != 0) (μ : Measure (ι -> Real)) [IsAddHaarMeasure μ] :
    Measure.map f μ = ENNReal.ofReal (abs (LinearMap.det f)⁻¹) • μ := by
  cases nonempty_fintype ι
  /- We have already proved the result for the Lebesgue product measure, using matrices.
    We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := addHaarMeasure_unique μ (piIcc01 ι)
  rw [this]; rw [addHaarMeasure_eq_volume_pi]; rw [Measure.map_smul]; rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hf]; rw [smul_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional Real E] (μ : Measure E) [IsAddHaarMeasure μ]

/--
theorem `map_linearMap_addHaar_eq_smul_addHaar` / 定理 `map_linearMap_addHaar_eq_smul_addHaar`

English:
theorem map_linearMap_addHaar_eq_smul_addHaar
  given: {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0)
  proof: by
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linearMap_addHaar_pi_eq_smul_addHaar`.
  let ι := Fin (finrank Real E)
  have : FiniteDimensional Real (ι -> Real) := by infer_instance
  have : finrank Real E = finrank Real (ι -> R

中文:
定理 map_linearMap_addHaar_eq_smul_addHaar
  条件: {f : E ->ₗ[实数] E} (hf : LinearMap.det f != 0)
  证明: by
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linearMap_addHaar_pi_eq_smul_addHaar`.
  let ι := Fin (finrank Real E)
  have : FiniteDimensional Real (ι -> Real) := by infer_instance
  have : finrank Real E = finrank Real (ι -> R
-/
theorem map_linearMap_addHaar_eq_smul_addHaar {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0) :
    Measure.map f μ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • μ := by
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linearMap_addHaar_pi_eq_smul_addHaar`.
  let ι := Fin (finrank Real E)
  have : FiniteDimensional Real (ι -> Real) := by infer_instance
  have : finrank Real E = finrank Real (ι -> Real) := by simp [ι]
  have e : E ≃ₗ[Real] ι -> Real := LinearEquiv.ofFinrankEq E (ι -> Real) this
  -- next line is to avoid `g` getting reduced by `simp`.
  obtain ⟨g, hg⟩ : exists g, g = (e : E ->ₗ[Real] ι -> Real).comp (f.comp (e.symm : (ι -> Real) ->ₗ[Real] E)) := ⟨_, rfl⟩
  have gdet : LinearMap.det g = LinearMap.det f := by rw [hg]; exact LinearMap.det_conj f e
  rw [← gdet] at hf ⊢
  have fg : f = (e.symm : (ι -> Real) ->ₗ[Real] E).comp (g.comp (e : E ->ₗ[Real] ι -> Real)) := by
    ext x
    simp only [LinearEquiv.coe_coe, Function.comp_apply, LinearMap.coe_comp,
      LinearEquiv.symm_apply_apply, hg]
  simp only [fg, LinearEquiv.coe_coe, LinearMap.coe_comp]
  have Ce : Continuous e := (e : E ->ₗ[Real] ι -> Real).continuous_of_finiteDimensional
  have Cg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have Cesymm : Continuous e.symm := (e.symm : (ι -> Real) ->ₗ[Real] E).continuous_of_finiteDimensional
  rw [← map_map Cesymm.measurable (Cg.comp Ce).measurable]; rw [← map_map Cg.measurable Ce.measurable]
  have : IsAddHaarMeasure (map e μ) := (e : E ≃+ (ι -> Real)).isAddHaarMeasure_map μ Ce Cesymm
  have ecomp : e.symm ∘ e = id := by
    ext x; simp only [id, Function.comp_apply, LinearEquiv.symm_apply_apply]
  rw [map_linearMap_addHaar_pi_eq_smul_addHaar hf (map e μ)]; rw [Measure.map_smul]; rw [map_map Cesymm.measurable Ce.measurable]; rw [ecomp]; rw [Measure.map_id]

/-- The preimage of a set `s` under a linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
/--
theorem `addHaar_preimage_linearMap` / 定理 `addHaar_preimage_linearMap`

English:
theorem addHaar_preimage_linearMap
  given: {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0) (s : Set E)
  proof: calc
    μ (f ⁻¹' s) = Measure.map f μ s :=
      ((f.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply
          s).symm
    _ = ENNReal.ofReal |(LinearMap.det f)⁻¹| * μ s := by
      rw [map_linearMap_addHaar_eq_smul_addHaar μ hf]; rfl

中文:
定理 addHaar_preimage_linearMap
  条件: {f : E ->ₗ[实数] E} (hf : LinearMap.det f != 0) (s : Set E)
  证明: calc
    μ (f ⁻¹' s) = Measure.map f μ s :=
      ((f.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply
          s).symm
    _ = ENNReal.ofReal |(LinearMap.det f)⁻¹| * μ s := by
      rw [map_linearMap_addHaar_eq_smul_addHaar μ hf]; rfl

Depends on / 依赖: ENNReal, ENNReal.ofReal, LinearMap, LinearMap.det, Measure, Measure.map, equivOfDetNeZero, f.equivOfDetNeZero, map_apply, map_linearMap_addHaar_eq_smul_addHaar, ofReal, toContinuousLinearEquiv, toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply, toHomeomorph, toMeasurableEquiv
-/
theorem addHaar_preimage_linearMap {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |(LinearMap.det f)⁻¹| * μ s :=
  calc
    μ (f ⁻¹' s) = Measure.map f μ s :=
      ((f.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply
          s).symm
    _ = ENNReal.ofReal |(LinearMap.det f)⁻¹| * μ s := by
      rw [map_linearMap_addHaar_eq_smul_addHaar μ hf]; rfl

/-- The preimage of a set `s` under a continuous linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
/--
theorem `addHaar_preimage_continuousLinearMap` / 定理 `addHaar_preimage_continuousLinearMap`

English:
theorem addHaar_preimage_continuousLinearMap
  statement: {f : E ->L[Real] E}
  proof: addHaar_preimage_linearMap μ hf s

中文:
定理 addHaar_preimage_continuousLinearMap
  结论: {f : E ->L[实数] E}
  证明: addHaar_preimage_linearMap μ hf s

Depends on / 依赖: addHaar_preimage_linearMap
-/
theorem addHaar_preimage_continuousLinearMap {f : E ->L[Real] E}
    (hf : LinearMap.det (f : E ->ₗ[Real] E) != 0) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal (abs (LinearMap.det (f : E ->ₗ[Real] E))⁻¹) * μ s :=
  addHaar_preimage_linearMap μ hf s

/-- The preimage of a set `s` under a linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
/--
theorem `addHaar_preimage_linearEquiv` / 定理 `addHaar_preimage_linearEquiv`

English:
theorem addHaar_preimage_linearEquiv
  given: (f : E ≃ₗ[Real] E) (s : Set E)
  proof: by
  have A : LinearMap.det (f : E ->ₗ[Real] E) != 0 := (LinearEquiv.isUnit_det' f).ne_zero
  convert! addHaar_preimage_linearMap μ A s
  simp only [LinearEquiv.det_coe_symm]

中文:
定理 addHaar_preimage_linearEquiv
  条件: (f : E ≃ₗ[实数] E) (s : Set E)
  证明: by
  have A : LinearMap.det (f : E ->ₗ[Real] E) != 0 := (LinearEquiv.isUnit_det' f).ne_zero
  convert! addHaar_preimage_linearMap μ A s
  simp only [LinearEquiv.det_coe_symm]

Depends on / 依赖: LinearEquiv, LinearEquiv.det_coe_symm, LinearEquiv.isUnit_det, LinearMap, LinearMap.det, addHaar_preimage_linearMap, convert, det_coe_symm, isUnit_det, ne_zero
-/
theorem addHaar_preimage_linearEquiv (f : E ≃ₗ[Real] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |LinearMap.det (f.symm : E ->ₗ[Real] E)| * μ s := by
  have A : LinearMap.det (f : E ->ₗ[Real] E) != 0 := (LinearEquiv.isUnit_det' f).ne_zero
  convert! addHaar_preimage_linearMap μ A s
  simp only [LinearEquiv.det_coe_symm]

/-- The preimage of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
/--
theorem `addHaar_preimage_continuousLinearEquiv` / 定理 `addHaar_preimage_continuousLinearEquiv`

English:
theorem addHaar_preimage_continuousLinearEquiv
  given: (f : E ≃L[Real] E) (s : Set E)
  proof: addHaar_preimage_linearEquiv μ _ s

中文:
定理 addHaar_preimage_continuousLinearEquiv
  条件: (f : E ≃L[实数] E) (s : Set E)
  证明: addHaar_preimage_linearEquiv μ _ s

Depends on / 依赖: addHaar_preimage_linearEquiv
-/
theorem addHaar_preimage_continuousLinearEquiv (f : E ≃L[Real] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |LinearMap.det (f.symm : E ->ₗ[Real] E)| * μ s :=
  addHaar_preimage_linearEquiv μ _ s

/-- The image of a set `s` under a linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
/--
theorem `addHaar_image_linearMap` / 定理 `addHaar_image_linearMap`

English:
theorem addHaar_image_linearMap
  given: (f : E ->ₗ[Real] E) (s : Set E)
  proof: by
  rcases ne_or_eq (LinearMap.det f) 0 with (hf | hf)
  · let g := (f.equivOfDetNeZero hf).toContinuousLinearEquiv
    change μ (g '' s) = _
    rw [ContinuousLinearEquiv.image_eq_preimage_symm g s]; rw [addHaar_preimage_continuousLinearEquiv]
    congr
· simpa [hf] using (measure_mono (image_subs

中文:
定理 addHaar_image_linearMap
  条件: (f : E ->ₗ[实数] E) (s : Set E)
  证明: by
  rcases ne_or_eq (LinearMap.det f) 0 with (hf | hf)
  · let g := (f.equivOfDetNeZero hf).toContinuousLinearEquiv
    change μ (g '' s) = _
    rw [ContinuousLinearEquiv.image_eq_preimage_symm g s]; rw [addHaar_preimage_continuousLinearEquiv]
    congr
· simpa [hf] using (measure_mono (image_subs

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.image_eq_preimage_symm, LinearMap, LinearMap.det, LinearMap.range_lt_top_of_det_eq_zero, addHaar_preimage_continuousLinearEquiv, addHaar_submodule, equivOfDetNeZero, f.equivOfDetNeZero, image_eq_preimage_symm, image_subset_range, measure_mono, ne_or_eq, range_lt_top_of_det_eq_zero, toContinuousLinearEquiv, trans_eq
-/
theorem addHaar_image_linearMap (f : E ->ₗ[Real] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f| * μ s := by
  rcases ne_or_eq (LinearMap.det f) 0 with (hf | hf)
  · let g := (f.equivOfDetNeZero hf).toContinuousLinearEquiv
    change μ (g '' s) = _
    rw [ContinuousLinearEquiv.image_eq_preimage_symm g s]; rw [addHaar_preimage_continuousLinearEquiv]
    congr
· simpa [hf] using (measure_mono (image_subset_range _ _)).trans_eq
      addHaar_submodule μ _ (LinearMap.range_lt_top_of_det_eq_zero hf).ne

/-- The image of a set `s` under a continuous linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
/--
theorem `addHaar_image_continuousLinearMap` / 定理 `addHaar_image_continuousLinearMap`

English:
theorem addHaar_image_continuousLinearMap
  given: (f : E ->L[Real] E) (s : Set E)
  proof: addHaar_image_linearMap μ _ s

中文:
定理 addHaar_image_continuousLinearMap
  条件: (f : E ->L[实数] E) (s : Set E)
  证明: addHaar_image_linearMap μ _ s

Depends on / 依赖: addHaar_image_linearMap
-/
theorem addHaar_image_continuousLinearMap (f : E ->L[Real] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f : E ->ₗ[Real] E)| * μ s :=
  addHaar_image_linearMap μ _ s

/-- The image of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
/--
theorem `addHaar_image_continuousLinearEquiv` / 定理 `addHaar_image_continuousLinearEquiv`

English:
theorem addHaar_image_continuousLinearEquiv
  given: (f : E ≃L[Real] E) (s : Set E)
  proof: μ.addHaar_image_linearMap (f : E ->ₗ[Real] E) s

中文:
定理 addHaar_image_continuousLinearEquiv
  条件: (f : E ≃L[实数] E) (s : Set E)
  证明: μ.addHaar_image_linearMap (f : E ->ₗ[Real] E) s

Depends on / 依赖: addHaar_image_linearMap
-/
theorem addHaar_image_continuousLinearEquiv (f : E ≃L[Real] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f : E ->ₗ[Real] E)| * μ s :=
  μ.addHaar_image_linearMap (f : E ->ₗ[Real] E) s

/--
theorem `LinearMap.quasiMeasurePreserving` / 定理 `LinearMap.quasiMeasurePreserving`

English:
theorem LinearMap.quasiMeasurePreserving
  given: (f : E ->ₗ[Real] E) (hf : LinearMap.det f != 0)
  proof: by
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [map_linearMap_addHaar_eq_smul_addHaar μ hf]
  exact smul_absolutelyContinuous

中文:
定理 LinearMap.quasiMeasurePreserving
  条件: (f : E ->ₗ[实数] E) (hf : LinearMap.det f != 0)
  证明: by
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [map_linearMap_addHaar_eq_smul_addHaar μ hf]
  exact smul_absolutelyContinuous

Depends on / 依赖: continuous_of_finiteDimensional, f.continuous_of_finiteDimensional.measurable, map_linearMap_addHaar_eq_smul_addHaar, measurable, smul_absolutelyContinuous
-/
theorem LinearMap.quasiMeasurePreserving (f : E ->ₗ[Real] E) (hf : LinearMap.det f != 0) :
    QuasiMeasurePreserving f μ μ := by
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [map_linearMap_addHaar_eq_smul_addHaar μ hf]
  exact smul_absolutelyContinuous

/--
theorem `ContinuousLinearMap.quasiMeasurePreserving` / 定理 `ContinuousLinearMap.quasiMeasurePreserving`

English:
theorem ContinuousLinearMap.quasiMeasurePreserving
  given: (f : E ->L[Real] E) (hf : f.det != 0)
  proof: LinearMap.quasiMeasurePreserving μ (f : E ->ₗ[Real] E) hf

中文:
定理 ContinuousLinearMap.quasiMeasurePreserving
  条件: (f : E ->L[实数] E) (hf : f.det != 0)
  证明: LinearMap.quasiMeasurePreserving μ (f : E ->ₗ[Real] E) hf

Depends on / 依赖: LinearMap, LinearMap.quasiMeasurePreserving, quasiMeasurePreserving
-/
theorem ContinuousLinearMap.quasiMeasurePreserving (f : E ->L[Real] E) (hf : f.det != 0) :
    QuasiMeasurePreserving f μ μ :=
  LinearMap.quasiMeasurePreserving μ (f : E ->ₗ[Real] E) hf



/--
theorem `map_addHaar_smul` / 定理 `map_addHaar_smul`

English:
theorem map_addHaar_smul
  given: {r : Real} (hr : r != 0)
  proof: by
  let f : E ->ₗ[Real] E := r • (1 : E ->ₗ[Real] E)
  change Measure.map f μ = _
  have hf : LinearMap.det f != 0 := by
    simp only [f, mul_one, LinearMap.det_smul, Ne, map_one]
    exact pow_ne_zero _ hr
  simp only [f, map_linearMap_addHaar_eq_smul_addHaar μ hf, mul_one, LinearMap.det_smul, ma

中文:
定理 map_addHaar_smul
  条件: {r : 实数} (hr : r != 0)
  证明: by
  let f : E ->ₗ[Real] E := r • (1 : E ->ₗ[Real] E)
  change Measure.map f μ = _
  have hf : LinearMap.det f != 0 := by
    simp only [f, mul_one, LinearMap.det_smul, Ne, map_one]
    exact pow_ne_zero _ hr
  simp only [f, map_linearMap_addHaar_eq_smul_addHaar μ hf, mul_one, LinearMap.det_smul, ma

Depends on / 依赖: LinearMap, LinearMap.det, LinearMap.det_smul, Measure, Measure.map, det_smul, map_linearMap_addHaar_eq_smul_addHaar, map_one, mul_one, pow_ne_zero
-/
theorem map_addHaar_smul {r : Real} (hr : r != 0) :
    Measure.map (r • ·) μ = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) • μ := by
  let f : E ->ₗ[Real] E := r • (1 : E ->ₗ[Real] E)
  change Measure.map f μ = _
  have hf : LinearMap.det f != 0 := by
    simp only [f, mul_one, LinearMap.det_smul, Ne, map_one]
    exact pow_ne_zero _ hr
  simp only [f, map_linearMap_addHaar_eq_smul_addHaar μ hf, mul_one, LinearMap.det_smul, map_one]

/--
theorem `quasiMeasurePreserving_smul` / 定理 `quasiMeasurePreserving_smul`

English:
theorem quasiMeasurePreserving_smul
  given: {r : Real} (hr : r != 0)
  proof: by
  refine ⟨measurable_const_smul r, ?_⟩
  rw [map_addHaar_smul μ hr]
  exact smul_absolutelyContinuous

@[simp]

中文:
定理 quasiMeasurePreserving_smul
  条件: {r : 实数} (hr : r != 0)
  证明: by
  refine ⟨measurable_const_smul r, ?_⟩
  rw [map_addHaar_smul μ hr]
  exact smul_absolutelyContinuous

@[simp]

Depends on / 依赖: map_addHaar_smul, measurable_const_smul, smul_absolutelyContinuous
-/
theorem quasiMeasurePreserving_smul {r : Real} (hr : r != 0) :
    QuasiMeasurePreserving (r • ·) μ μ := by
  refine ⟨measurable_const_smul r, ?_⟩
  rw [map_addHaar_smul μ hr]
  exact smul_absolutelyContinuous

@[simp]
/--
theorem `addHaar_preimage_smul` / 定理 `addHaar_preimage_smul`

English:
theorem addHaar_preimage_smul
  given: {r : Real} (hr : r != 0) (s : Set E)
  proof: calc
    μ ((r • ·) ⁻¹' s) = Measure.map (r • ·) μ s :=
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) * μ s := by
      rw [map_addHaar_smul μ hr]; rw [coe_smul]; rw [Pi.smul_apply]; rw [smul_eq_mul]

中文:
定理 addHaar_preimage_smul
  条件: {r : 实数} (hr : r != 0) (s : Set E)
  证明: calc
    μ ((r • ·) ⁻¹' s) = Measure.map (r • ·) μ s :=
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) * μ s := by
      rw [map_addHaar_smul μ hr]; rw [coe_smul]; rw [Pi.smul_apply]; rw [smul_eq_mul]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Homeomorph, Homeomorph.smul, Measure, Measure.map, Pi.smul_apply, coe_smul, finrank, isUnit_iff_ne_zero, map_addHaar_smul, map_apply, ofReal, smul_apply, smul_eq_mul, toMeasurableEquiv, toMeasurableEquiv.map_apply
-/
theorem addHaar_preimage_smul {r : Real} (hr : r != 0) (s : Set E) :
    μ ((r • ·) ⁻¹' s) = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) * μ s :=
  calc
    μ ((r • ·) ⁻¹' s) = Measure.map (r • ·) μ s :=
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) * μ s := by
      rw [map_addHaar_smul μ hr]; rw [coe_smul]; rw [Pi.smul_apply]; rw [smul_eq_mul]

/-- Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`. -/
@[simp]
/--
theorem `addHaar_smul` / 定理 `addHaar_smul`

English:
theorem addHaar_smul
  given: (r : Real) (s : Set E)
  proof: by
  rcases ne_or_eq r 0 with (h | rfl)
  · rw [← preimage_smul_inv₀ h, addHaar_preimage_smul μ (inv_ne_zero h), inv_pow, inv_inv]
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp only [measure_empty, mul_zero, smul_set_empty]
  rw [zero_smul_set hs]; rw [← singleton_zero]
  by_cases h : fin

中文:
定理 addHaar_smul
  条件: (r : 实数) (s : Set E)
  证明: by
  rcases ne_or_eq r 0 with (h | rfl)
  · rw [← preimage_smul_inv₀ h, addHaar_preimage_smul μ (inv_ne_zero h), inv_pow, inv_inv]
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp only [measure_empty, mul_zero, smul_set_empty]
  rw [zero_smul_set hs]; rw [← singleton_zero]
  by_cases h : fin

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, Subsingleton, Subsingleton.eq_univ_of_nonempty, abs_one, addHaar_preimage_smul, eq_empty_or_nonempty, eq_univ_of_nonempty, finrank, finrank_zero_iff, inv_inv, inv_ne_zero, inv_pow, measure_empty, mul_zero, ne_or_eq, ofReal_one, one_mul, pow_zero, singleton_nonem
-/
theorem addHaar_smul (r : Real) (s : Set E) :
    μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s := by
  rcases ne_or_eq r 0 with (h | rfl)
  · rw [← preimage_smul_inv₀ h, addHaar_preimage_smul μ (inv_ne_zero h), inv_pow, inv_inv]
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp only [measure_empty, mul_zero, smul_set_empty]
  rw [zero_smul_set hs]; rw [← singleton_zero]
  by_cases h : finrank Real E = 0
  · have : Subsingleton E := finrank_zero_iff.1 h
    simp only [h, one_mul, ENNReal.ofReal_one, abs_one, Subsingleton.eq_univ_of_nonempty hs,
      pow_zero, Subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E))]
  · have : Nontrivial E := nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h)
    simp only [h, zero_mul, ENNReal.ofReal_zero, abs_zero, Ne, not_false_iff,
      zero_pow, measure_singleton]

/--
theorem `addHaar_smul_of_nonneg` / 定理 `addHaar_smul_of_nonneg`

English:
theorem addHaar_smul_of_nonneg
  given: {r : Real} (hr : 0 <= r) (s : Set E)
  proof: by
  rw [addHaar_smul]; rw [abs_pow]; rw [abs_of_nonneg hr]

@[simp]

中文:
定理 addHaar_smul_of_nonneg
  条件: {r : 实数} (hr : 0 <= r) (s : Set E)
  证明: by
  rw [addHaar_smul]; rw [abs_pow]; rw [abs_of_nonneg hr]

@[simp]

Depends on / 依赖: abs_of_nonneg, abs_pow, addHaar_smul
-/
theorem addHaar_smul_of_nonneg {r : Real} (hr : 0 <= r) (s : Set E) :
    μ (r • s) = ENNReal.ofReal (r ^ finrank Real E) * μ s := by
  rw [addHaar_smul]; rw [abs_pow]; rw [abs_of_nonneg hr]

@[simp]
/--
theorem `addHaar_nnreal_smul` / 定理 `addHaar_nnreal_smul`

English:
theorem addHaar_nnreal_smul
  given: (r : Real>=0) (s : Set E)
  proof: by
  simp [NNReal.smul_def]

中文:
定理 addHaar_nnreal_smul
  条件: (r : 实数>=0) (s : Set E)
  证明: by
  simp [NNReal.smul_def]

Depends on / 依赖: NNReal, NNReal.smul_def, smul_def
-/
theorem addHaar_nnreal_smul (r : Real>=0) (s : Set E) :
    μ (r • s) = r ^ Module.finrank Real E * μ s := by
  simp [NNReal.smul_def]

variable {μ} {s : Set E}

-- Note: We might want to rename this once we acquire the lemma corresponding to
-- `MeasurableSet.const_smul`
/--
theorem `NullMeasurableSet.const_smul` / 定理 `NullMeasurableSet.const_smul`

English:
theorem NullMeasurableSet.const_smul
  given: (hs : NullMeasurableSet s μ) (r : Real)
  proof: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | hr := eq_or_ne r 0
  · simpa [zero_smul_set hs'] using! nullMeasurableSet_singleton _
  obtain ⟨t, ht, hst⟩ := hs
  refine ⟨_, ht.const_smul_of_ne_zero hr, ?_⟩
  rw [← measure_symmDiff_eq_zero_iff] at hst ⊢
  rw [← smul_set_symm

中文:
定理 NullMeasurableSet.const_smul
  条件: (hs : NullMeasurableSet s μ) (r : 实数)
  证明: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | hr := eq_or_ne r 0
  · simpa [zero_smul_set hs'] using! nullMeasurableSet_singleton _
  obtain ⟨t, ht, hst⟩ := hs
  refine ⟨_, ht.const_smul_of_ne_zero hr, ?_⟩
  rw [← measure_symmDiff_eq_zero_iff] at hst ⊢
  rw [← smul_set_symm

Depends on / 依赖: addHaar_smul, const_smul_of_ne_zero, eq_empty_or_nonempty, eq_or_ne, ht.const_smul_of_ne_zero, measure_symmDiff_eq_zero_iff, mul_zero, nullMeasurableSet_singleton, s.eq_empty_or_nonempty, zero_smul_set
-/
theorem NullMeasurableSet.const_smul (hs : NullMeasurableSet s μ) (r : Real) :
    NullMeasurableSet (r • s) μ := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | hr := eq_or_ne r 0
  · simpa [zero_smul_set hs'] using! nullMeasurableSet_singleton _
  obtain ⟨t, ht, hst⟩ := hs
  refine ⟨_, ht.const_smul_of_ne_zero hr, ?_⟩
  rw [← measure_symmDiff_eq_zero_iff] at hst ⊢
  rw [← smul_set_symmDiff₀ hr]; rw [addHaar_smul μ]; rw [hst]; rw [mul_zero]

variable (μ)

@[simp]
/--
theorem `addHaar_image_homothety` / 定理 `addHaar_image_homothety`

English:
theorem addHaar_image_homothety
  given: (x : E) (r : Real) (s : Set E)
  proof: calc
    μ (AffineMap.homothety x r '' s) = μ ((fun y => y + x) '' (r • (fun y => y + -x) '' s)) := by
      simp only [← image_smul, image_image, ← sub_eq_add_neg]; rfl
    _ = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s := by
      simp only [image_add_right, measure_preimage_add_right, addHaa

中文:
定理 addHaar_image_homothety
  条件: (x : E) (r : 实数) (s : Set E)
  证明: calc
    μ (AffineMap.homothety x r '' s) = μ ((fun y => y + x) '' (r • (fun y => y + -x) '' s)) := by
      simp only [← image_smul, image_image, ← sub_eq_add_neg]; rfl
    _ = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s := by
      simp only [image_add_right, measure_preimage_add_right, addHaa

Depends on / 依赖: AffineMap, AffineMap.homothety, ENNReal, ENNReal.ofReal, addHaar_smul, finrank, homothety, image_add_right, image_image, image_smul, measure_preimage_add_right, ofReal, sub_eq_add_neg
-/
theorem addHaar_image_homothety (x : E) (r : Real) (s : Set E) :
    μ (AffineMap.homothety x r '' s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s :=
  calc
    μ (AffineMap.homothety x r '' s) = μ ((fun y => y + x) '' (r • (fun y => y + -x) '' s)) := by
      simp only [← image_smul, image_image, ← sub_eq_add_neg]; rfl
    _ = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s := by
      simp only [image_add_right, measure_preimage_add_right, addHaar_smul]

/-! We don't need to state `map_addHaar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/



/--
theorem `addHaar_ball_center` / 定理 `addHaar_ball_center`

English:
theorem addHaar_ball_center
  statement: {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  proof: by
  have : ball (0 : E) r = (x + ·) ⁻¹' ball x r := by simp [preimage_add_ball]
  rw [this]; rw [measure_preimage_add]

中文:
定理 addHaar_ball_center
  结论: {E : 类型} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  证明: by
  have : ball (0 : E) r = (x + ·) ⁻¹' ball x r := by simp [preimage_add_ball]
  rw [this]; rw [measure_preimage_add]

Depends on / 依赖: measure_preimage_add, preimage_add_ball
-/
theorem addHaar_ball_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : Real) : μ (ball x r) = μ (ball (0 : E) r) := by
  have : ball (0 : E) r = (x + ·) ⁻¹' ball x r := by simp [preimage_add_ball]
  rw [this]; rw [measure_preimage_add]

/--
theorem `addHaar_real_ball_center` / 定理 `addHaar_real_ball_center`

English:
theorem addHaar_real_ball_center
  statement: {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  proof: by
  simp [measureReal_def, addHaar_ball_center]

中文:
定理 addHaar_real_ball_center
  结论: {E : 类型} [NormedAddCommGroup E] [MeasurableSpace E]
  证明: by
  simp [measureReal_def, addHaar_ball_center]

Depends on / 依赖: addHaar_ball_center, measureReal_def
-/
theorem addHaar_real_ball_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : Real) :
    μ.real (ball x r) = μ.real (ball (0 : E) r) := by
  simp [measureReal_def, addHaar_ball_center]

/--
theorem `addHaar_closedBall_center` / 定理 `addHaar_closedBall_center`

English:
theorem addHaar_closedBall_center
  statement: {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  proof: by
  have : closedBall (0 : E) r = (x + ·) ⁻¹' closedBall x r := by simp [preimage_add_closedBall]
  rw [this]; rw [measure_preimage_add]

中文:
定理 addHaar_closedBall_center
  结论: {E : 类型} [NormedAddCommGroup E] [MeasurableSpace E]
  证明: by
  have : closedBall (0 : E) r = (x + ·) ⁻¹' closedBall x r := by simp [preimage_add_closedBall]
  rw [this]; rw [measure_preimage_add]

Depends on / 依赖: closedBall, measure_preimage_add, preimage_add_closedBall
-/
theorem addHaar_closedBall_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : Real) :
    μ (closedBall x r) = μ (closedBall (0 : E) r) := by
  have : closedBall (0 : E) r = (x + ·) ⁻¹' closedBall x r := by simp [preimage_add_closedBall]
  rw [this]; rw [measure_preimage_add]

/--
theorem `addHaar_real_closedBall_center` / 定理 `addHaar_real_closedBall_center`

English:
theorem addHaar_real_closedBall_center
  statement: {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  proof: by
  simp [measureReal_def, addHaar_closedBall_center]

中文:
定理 addHaar_real_closedBall_center
  结论: {E : 类型} [NormedAddCommGroup E] [MeasurableSpace E]
  证明: by
  simp [measureReal_def, addHaar_closedBall_center]

Depends on / 依赖: addHaar_closedBall_center, measureReal_def
-/
theorem addHaar_real_closedBall_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : Real) :
    μ.real (closedBall x r) = μ.real (closedBall (0 : E) r) := by
  simp [measureReal_def, addHaar_closedBall_center]

/--
theorem `addHaar_ball_mul_of_pos` / 定理 `addHaar_ball_mul_of_pos`

English:
theorem addHaar_ball_mul_of_pos
  given: (x : E) {r : Real} (hr : 0 < r) (s : Real)
  proof: by
  have : ball (0 : E) (r * s) = r • ball (0 : E) s := by
    simp only [_root_.smul_ball hr.ne' (0 : E) s, Real.norm_eq_abs, abs_of_nonneg hr.le, smul_zero]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_ball_center, abs_pow]

中文:
定理 addHaar_ball_mul_of_pos
  条件: (x : E) {r : 实数} (hr : 0 < r) (s : 实数)
  证明: by
  have : ball (0 : E) (r * s) = r • ball (0 : E) s := by
    simp only [_root_.smul_ball hr.ne' (0 : E) s, Real.norm_eq_abs, abs_of_nonneg hr.le, smul_zero]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_ball_center, abs_pow]

Depends on / 依赖: Real.norm_eq_abs, _root_, _root_.smul_ball, abs_of_nonneg, abs_pow, addHaar_ball_center, addHaar_smul, hr.le, hr.ne, norm_eq_abs, smul_ball, smul_zero
-/
theorem addHaar_ball_mul_of_pos (x : E) {r : Real} (hr : 0 < r) (s : Real) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank Real E) * μ (ball 0 s) := by
  have : ball (0 : E) (r * s) = r • ball (0 : E) s := by
    simp only [_root_.smul_ball hr.ne' (0 : E) s, Real.norm_eq_abs, abs_of_nonneg hr.le, smul_zero]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_ball_center, abs_pow]

/--
theorem `addHaar_ball_of_pos` / 定理 `addHaar_ball_of_pos`

English:
theorem addHaar_ball_of_pos
  given: (x : E) {r : Real} (hr : 0 < r)
  proof: by
  rw [← addHaar_ball_mul_of_pos μ x hr]; rw [mul_one]

中文:
定理 addHaar_ball_of_pos
  条件: (x : E) {r : 实数} (hr : 0 < r)
  证明: by
  rw [← addHaar_ball_mul_of_pos μ x hr]; rw [mul_one]

Depends on / 依赖: addHaar_ball_mul_of_pos, mul_one
-/
theorem addHaar_ball_of_pos (x : E) {r : Real} (hr : 0 < r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank Real E) * μ (ball 0 1) := by
  rw [← addHaar_ball_mul_of_pos μ x hr]; rw [mul_one]

/--
theorem `addHaar_ball_mul` / 定理 `addHaar_ball_mul`

English:
theorem addHaar_ball_mul
  given: [Nontrivial E] (x : E) {r : Real} (hr : 0 <= r) (s : Real)
  proof: by
  rcases hr.eq_or_lt with (rfl | h)
  · simp only [zero_pow (finrank_pos (R := Real) (M := E)).ne', measure_empty, zero_mul,
      ENNReal.ofReal_zero, ball_zero]
  · exact addHaar_ball_mul_of_pos μ x h s

中文:
定理 addHaar_ball_mul
  条件: [Nontrivial E] (x : E) {r : 实数} (hr : 0 <= r) (s : 实数)
  证明: by
  rcases hr.eq_or_lt with (rfl | h)
  · simp only [zero_pow (finrank_pos (R := Real) (M := E)).ne', measure_empty, zero_mul,
      ENNReal.ofReal_zero, ball_zero]
  · exact addHaar_ball_mul_of_pos μ x h s

Depends on / 依赖: ENNReal, ENNReal.ofReal_zero, addHaar_ball_mul_of_pos, ball_zero, eq_or_lt, finrank_pos, hr.eq_or_lt, measure_empty, ofReal_zero, zero_mul, zero_pow
-/
theorem addHaar_ball_mul [Nontrivial E] (x : E) {r : Real} (hr : 0 <= r) (s : Real) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank Real E) * μ (ball 0 s) := by
  rcases hr.eq_or_lt with (rfl | h)
  · simp only [zero_pow (finrank_pos (R := Real) (M := E)).ne', measure_empty, zero_mul,
      ENNReal.ofReal_zero, ball_zero]
  · exact addHaar_ball_mul_of_pos μ x h s

/--
theorem `addHaar_ball` / 定理 `addHaar_ball`

English:
theorem addHaar_ball
  given: [Nontrivial E] (x : E) {r : Real} (hr : 0 <= r)
  proof: by
  rw [← addHaar_ball_mul μ x hr]; rw [mul_one]

中文:
定理 addHaar_ball
  条件: [Nontrivial E] (x : E) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [← addHaar_ball_mul μ x hr]; rw [mul_one]

Depends on / 依赖: addHaar_ball_mul, mul_one
-/
theorem addHaar_ball [Nontrivial E] (x : E) {r : Real} (hr : 0 <= r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank Real E) * μ (ball 0 1) := by
  rw [← addHaar_ball_mul μ x hr]; rw [mul_one]

/--
theorem `addHaar_closedBall_mul_of_pos` / 定理 `addHaar_closedBall_mul_of_pos`

English:
theorem addHaar_closedBall_mul_of_pos
  given: (x : E) {r : Real} (hr : 0 < r) (s : Real)
  proof: by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall' hr.ne' (0 : E), abs_of_nonneg hr.le]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_closedBall_center, abs_pow]

中文:
定理 addHaar_closedBall_mul_of_pos
  条件: (x : E) {r : 实数} (hr : 0 < r) (s : 实数)
  证明: by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall' hr.ne' (0 : E), abs_of_nonneg hr.le]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_closedBall_center, abs_pow]

Depends on / 依赖: abs_of_nonneg, abs_pow, addHaar_closedBall_center, addHaar_smul, closedBall, hr.le, hr.ne, smul_closedBall
-/
theorem addHaar_closedBall_mul_of_pos (x : E) {r : Real} (hr : 0 < r) (s : Real) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank Real E) * μ (closedBall 0 s) := by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall' hr.ne' (0 : E), abs_of_nonneg hr.le]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_closedBall_center, abs_pow]

/--
theorem `addHaar_closedBall_mul` / 定理 `addHaar_closedBall_mul`

English:
theorem addHaar_closedBall_mul
  given: (x : E) {r : Real} (hr : 0 <= r) {s : Real} (hs : 0 <= s)
  proof: by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall r (0 : E) hs, abs_of_nonneg hr]
  simp only [this, addHaar_smul, abs_of_nonneg hr, addHaar_closedBall_center, abs_pow]

中文:
定理 addHaar_closedBall_mul
  条件: (x : E) {r : 实数} (hr : 0 <= r) {s : 实数} (hs : 0 <= s)
  证明: by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall r (0 : E) hs, abs_of_nonneg hr]
  simp only [this, addHaar_smul, abs_of_nonneg hr, addHaar_closedBall_center, abs_pow]

Depends on / 依赖: abs_of_nonneg, abs_pow, addHaar_closedBall_center, addHaar_smul, closedBall, smul_closedBall
-/
theorem addHaar_closedBall_mul (x : E) {r : Real} (hr : 0 <= r) {s : Real} (hs : 0 <= s) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank Real E) * μ (closedBall 0 s) := by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall r (0 : E) hs, abs_of_nonneg hr]
  simp only [this, addHaar_smul, abs_of_nonneg hr, addHaar_closedBall_center, abs_pow]

/--
theorem `addHaar_closedBall'` / 定理 `addHaar_closedBall'`

English:
theorem addHaar_closedBall'
  given: (x : E) {r : Real} (hr : 0 <= r)
  proof: by
  rw [← addHaar_closedBall_mul μ x hr zero_le_one]; rw [mul_one]

中文:
定理 addHaar_closedBall'
  条件: (x : E) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [← addHaar_closedBall_mul μ x hr zero_le_one]; rw [mul_one]

Depends on / 依赖: addHaar_closedBall_mul, mul_one, zero_le_one
-/
theorem addHaar_closedBall' (x : E) {r : Real} (hr : 0 <= r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank Real E) * μ (closedBall 0 1) := by
  rw [← addHaar_closedBall_mul μ x hr zero_le_one]; rw [mul_one]

/--
theorem `addHaar_real_closedBall'` / 定理 `addHaar_real_closedBall'`

English:
theorem addHaar_real_closedBall'
  given: (x : E) {r : Real} (hr : 0 <= r)
  proof: by
  simp only [measureReal_def, addHaar_closedBall' μ x hr, ENNReal.toReal_mul, mul_eq_mul_right_iff,
    ENNReal.toReal_ofReal_eq_iff]
  left
  positivity

中文:
定理 addHaar_real_closedBall'
  条件: (x : E) {r : 实数} (hr : 0 <= r)
  证明: by
  simp only [measureReal_def, addHaar_closedBall' μ x hr, ENNReal.toReal_mul, mul_eq_mul_right_iff,
    ENNReal.toReal_ofReal_eq_iff]
  left
  positivity

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal_eq_iff, addHaar_closedBall, measureReal_def, mul_eq_mul_right_iff, toReal_mul, toReal_ofReal_eq_iff
-/
theorem addHaar_real_closedBall' (x : E) {r : Real} (hr : 0 <= r) :
    μ.real (closedBall x r) = r ^ finrank Real E * μ.real (closedBall 0 1) := by
  simp only [measureReal_def, addHaar_closedBall' μ x hr, ENNReal.toReal_mul, mul_eq_mul_right_iff,
    ENNReal.toReal_ofReal_eq_iff]
  left
  positivity

/--
theorem `addHaar_unitClosedBall_eq_addHaar_unitBall` / 定理 `addHaar_unitClosedBall_eq_addHaar_unitBall`

English:
theorem addHaar_unitClosedBall_eq_addHaar_unitBall
  proof: by
  apply le_antisymm _ (measure_mono ball_subset_closedBall)
  have A : Tendsto
      (fun r : Real => ENNReal.ofReal (r ^ finrank Real E) * μ (closedBall (0 : E) 1)) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal ((1 : Real) ^ finrank Real E) * μ (closedBall (0 : E) 1))) := by
    refine ENNReal.Tendsto.mul

中文:
定理 addHaar_unitClosedBall_eq_addHaar_unitBall
  证明: by
  apply le_antisymm _ (measure_mono ball_subset_closedBall)
  have A : Tendsto
      (fun r : Real => ENNReal.ofReal (r ^ finrank Real E) * μ (closedBall (0 : E) 1)) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal ((1 : Real) ^ finrank Real E) * μ (closedBall (0 : E) 1))) := by
    refine ENNReal.Tendsto.mul

Depends on / 依赖: ENNReal, ENNReal.Tendsto.mul, ENNReal.ofReal, ENNReal.ofReal_one, ENNReal.tendsto_ofReal, Ioo_mem_nhd, Tendsto, ball_subset_closedBall, closedBall, filter_upwards, finrank, le_antisymm, le_of_tendsto, measure_mono, nhdsWithin_le_nhds, ofReal, ofReal_one, one_mul, one_pow, tendsto_const_nhds
-/
theorem addHaar_unitClosedBall_eq_addHaar_unitBall :
    μ (closedBall (0 : E) 1) = μ (ball 0 1) := by
  apply le_antisymm _ (measure_mono ball_subset_closedBall)
  have A : Tendsto
      (fun r : Real => ENNReal.ofReal (r ^ finrank Real E) * μ (closedBall (0 : E) 1)) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal ((1 : Real) ^ finrank Real E) * μ (closedBall (0 : E) 1))) := by
    refine ENNReal.Tendsto.mul ?_ (by simp) tendsto_const_nhds (by simp)
    exact ENNReal.tendsto_ofReal ((tendsto_id'.2 nhdsWithin_le_nhds).pow _)
  simp only [one_pow, one_mul, ENNReal.ofReal_one] at A
  refine le_of_tendsto A ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  rw [← addHaar_closedBall' μ (0 : E) hr.1.le]
  exact measure_mono (closedBall_subset_ball hr.2)

/--
theorem `addHaar_closedBall` / 定理 `addHaar_closedBall`

English:
theorem addHaar_closedBall
  given: (x : E) {r : Real} (hr : 0 <= r)
  proof: by
  rw [addHaar_closedBall' μ x hr]; rw [addHaar_unitClosedBall_eq_addHaar_unitBall]

中文:
定理 addHaar_closedBall
  条件: (x : E) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [addHaar_closedBall' μ x hr]; rw [addHaar_unitClosedBall_eq_addHaar_unitBall]

Depends on / 依赖: addHaar_closedBall, addHaar_unitClosedBall_eq_addHaar_unitBall
-/
theorem addHaar_closedBall (x : E) {r : Real} (hr : 0 <= r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank Real E) * μ (ball 0 1) := by
  rw [addHaar_closedBall' μ x hr]; rw [addHaar_unitClosedBall_eq_addHaar_unitBall]

/--
theorem `addHaar_real_closedBall` / 定理 `addHaar_real_closedBall`

English:
theorem addHaar_real_closedBall
  given: (x : E) {r : Real} (hr : 0 <= r)
  proof: by
  simp [addHaar_real_closedBall' μ x hr, measureReal_def,
    addHaar_unitClosedBall_eq_addHaar_unitBall]

中文:
定理 addHaar_real_closedBall
  条件: (x : E) {r : 实数} (hr : 0 <= r)
  证明: by
  simp [addHaar_real_closedBall' μ x hr, measureReal_def,
    addHaar_unitClosedBall_eq_addHaar_unitBall]

Depends on / 依赖: addHaar_real_closedBall, addHaar_unitClosedBall_eq_addHaar_unitBall, measureReal_def
-/
theorem addHaar_real_closedBall (x : E) {r : Real} (hr : 0 <= r) :
    μ.real (closedBall x r) = r ^ finrank Real E * μ.real (ball 0 1) := by
  simp [addHaar_real_closedBall' μ x hr, measureReal_def,
    addHaar_unitClosedBall_eq_addHaar_unitBall]

/--
theorem `addHaar_closedBall_eq_addHaar_ball` / 定理 `addHaar_closedBall_eq_addHaar_ball`

English:
theorem addHaar_closedBall_eq_addHaar_ball
  given: [Nontrivial E] (x : E) (r : Real)
  proof: by
  by_cases! h : r < 0
  · rw [Metric.closedBall_eq_empty.mpr h, Metric.ball_eq_empty.mpr h.le]
  rw [addHaar_closedBall μ x h]; rw [addHaar_ball μ x h]

中文:
定理 addHaar_closedBall_eq_addHaar_ball
  条件: [Nontrivial E] (x : E) (r : 实数)
  证明: by
  by_cases! h : r < 0
  · rw [Metric.closedBall_eq_empty.mpr h, Metric.ball_eq_empty.mpr h.le]
  rw [addHaar_closedBall μ x h]; rw [addHaar_ball μ x h]

Depends on / 依赖: Metric, Metric.ball_eq_empty.mpr, Metric.closedBall_eq_empty.mpr, addHaar_ball, addHaar_closedBall, ball_eq_empty, closedBall_eq_empty, h.le
-/
theorem addHaar_closedBall_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) :
    μ (closedBall x r) = μ (ball x r) := by
  by_cases! h : r < 0
  · rw [Metric.closedBall_eq_empty.mpr h, Metric.ball_eq_empty.mpr h.le]
  rw [addHaar_closedBall μ x h]; rw [addHaar_ball μ x h]

/--
theorem `addHaar_real_closedBall_eq_addHaar_real_ball` / 定理 `addHaar_real_closedBall_eq_addHaar_real_ball`

English:
theorem addHaar_real_closedBall_eq_addHaar_real_ball
  given: [Nontrivial E] (x : E) (r : Real)
  proof: by
  simp [measureReal_def, addHaar_closedBall_eq_addHaar_ball μ x r]

中文:
定理 addHaar_real_closedBall_eq_addHaar_real_ball
  条件: [Nontrivial E] (x : E) (r : 实数)
  证明: by
  simp [measureReal_def, addHaar_closedBall_eq_addHaar_ball μ x r]

Depends on / 依赖: addHaar_closedBall_eq_addHaar_ball, measureReal_def
-/
theorem addHaar_real_closedBall_eq_addHaar_real_ball [Nontrivial E] (x : E) (r : Real) :
    μ.real (closedBall x r) = μ.real (ball x r) := by
  simp [measureReal_def, addHaar_closedBall_eq_addHaar_ball μ x r]

/--
theorem `addHaar_sphere_of_ne_zero` / 定理 `addHaar_sphere_of_ne_zero`

English:
theorem addHaar_sphere_of_ne_zero
  given: (x : E) {r : Real} (hr : r != 0)
  statement: μ (sphere x r) = 0
  proof: by
  rcases hr.lt_or_gt with (h | h)
  · simp only [empty_sdiff, measure_empty, ← closedBall_sdiff_ball, closedBall_eq_empty.2 h]
  · rw [← closedBall_sdiff_ball,
      measure_sdiff ball_subset_closedBall measurableSet_ball.nullMeasurableSet
        measure_ball_lt_top.ne,
      addHaar_ball_of_pos

中文:
定理 addHaar_sphere_of_ne_zero
  条件: (x : E) {r : 实数} (hr : r != 0)
  结论: μ (sphere x r) = 0
  证明: by
  rcases hr.lt_or_gt with (h | h)
  · simp only [empty_sdiff, measure_empty, ← closedBall_sdiff_ball, closedBall_eq_empty.2 h]
  · rw [← closedBall_sdiff_ball,
      measure_sdiff ball_subset_closedBall measurableSet_ball.nullMeasurableSet
        measure_ball_lt_top.ne,
      addHaar_ball_of_pos

Depends on / 依赖: addHaar_ball_of_pos, addHaar_closedBall, ball_subset_closedBall, closedBall_eq_empty, closedBall_sdiff_ball, empty_sdiff, h.le, hr.lt_or_gt, lt_or_gt, measurableSet_ball, measurableSet_ball.nullMeasurableSet, measure_ball_lt_top, measure_ball_lt_top.ne, measure_empty, measure_sdiff, nullMeasurableSet, tsub_self
-/
theorem addHaar_sphere_of_ne_zero (x : E) {r : Real} (hr : r != 0) : μ (sphere x r) = 0 := by
  rcases hr.lt_or_gt with (h | h)
  · simp only [empty_sdiff, measure_empty, ← closedBall_sdiff_ball, closedBall_eq_empty.2 h]
  · rw [← closedBall_sdiff_ball,
      measure_sdiff ball_subset_closedBall measurableSet_ball.nullMeasurableSet
        measure_ball_lt_top.ne,
      addHaar_ball_of_pos μ _ h, addHaar_closedBall μ _ h.le, tsub_self]

/--
theorem `addHaar_sphere` / 定理 `addHaar_sphere`

English:
theorem addHaar_sphere
  given: [Nontrivial E] (x : E) (r : Real)
  statement: μ (sphere x r) = 0
  proof: by
  rcases eq_or_ne r 0 with (rfl | h)
  · rw [sphere_zero, measure_singleton]
  · exact addHaar_sphere_of_ne_zero μ x h

中文:
定理 addHaar_sphere
  条件: [Nontrivial E] (x : E) (r : 实数)
  结论: μ (sphere x r) = 0
  证明: by
  rcases eq_or_ne r 0 with (rfl | h)
  · rw [sphere_zero, measure_singleton]
  · exact addHaar_sphere_of_ne_zero μ x h

Depends on / 依赖: addHaar_sphere_of_ne_zero, eq_or_ne, measure_singleton, sphere_zero
-/
theorem addHaar_sphere [Nontrivial E] (x : E) (r : Real) : μ (sphere x r) = 0 := by
  rcases eq_or_ne r 0 with (rfl | h)
  · rw [sphere_zero, measure_singleton]
  · exact addHaar_sphere_of_ne_zero μ x h

/--
theorem `addHaar_singleton_add_smul_div_singleton_add_smul` / 定理 `addHaar_singleton_add_smul_div_singleton_add_smul`

English:
theorem addHaar_singleton_add_smul_div_singleton_add_smul
  statement: {r : Real} (hr : r != 0) (x y : E)
  proof: calc
    μ ({x} + r • s) / μ ({y} + r • t) = ENNReal.ofReal (|r| ^ finrank Real E) * μ s *
        (ENNReal.ofReal (|r| ^ finrank Real E) * μ t)⁻¹ := by
      simp only [div_eq_mul_inv, addHaar_smul, image_add_left, measure_preimage_add, abs_pow,
        singleton_add]
    _ = ENNReal.ofReal (|r| ^ 

中文:
定理 addHaar_singleton_add_smul_div_singleton_add_smul
  结论: {r : 实数} (hr : r != 0) (x y : E)
  证明: calc
    μ ({x} + r • s) / μ ({y} + r • t) = ENNReal.ofReal (|r| ^ finrank Real E) * μ s *
        (ENNReal.ofReal (|r| ^ finrank Real E) * μ t)⁻¹ := by
      simp only [div_eq_mul_inv, addHaar_smul, image_add_left, measure_preimage_add, abs_pow,
        singleton_add]
    _ = ENNReal.ofReal (|r| ^ 

Depends on / 依赖: ENNReal, ENNReal.mul_inv, ENNReal.ofReal, ENNReal.ofReal_eq_zero, ENNReal.ofReal_ne_top, abs_pos, abs_pos.mpr, abs_pow, addHaar_smul, div_eq_mul_inv, finrank, image_add_left, measure_preimage_add, mul_inv, not_le, ofReal, ofReal_eq_zero, ofReal_ne_top, pow_pos, singleton_add
-/
theorem addHaar_singleton_add_smul_div_singleton_add_smul {r : Real} (hr : r != 0) (x y : E)
    (s t : Set E) : μ ({x} + r • s) / μ ({y} + r • t) = μ s / μ t :=
  calc
    μ ({x} + r • s) / μ ({y} + r • t) = ENNReal.ofReal (|r| ^ finrank Real E) * μ s *
        (ENNReal.ofReal (|r| ^ finrank Real E) * μ t)⁻¹ := by
      simp only [div_eq_mul_inv, addHaar_smul, image_add_left, measure_preimage_add, abs_pow,
        singleton_add]
    _ = ENNReal.ofReal (|r| ^ finrank Real E) * (ENNReal.ofReal (|r| ^ finrank Real E))⁻¹ *
          (μ s * (μ t)⁻¹) := by
      rw [ENNReal.mul_inv]
      · ring
      · simp only [pow_pos (abs_pos.mpr hr), ENNReal.ofReal_eq_zero, not_le, Ne, true_or]
      · simp only [ENNReal.ofReal_ne_top, true_or, Ne, not_false_iff]
    _ = μ s / μ t := by
      rw [ENNReal.mul_inv_cancel]; rw [one_mul]; rw [div_eq_mul_inv]
      · simp only [pow_pos (abs_pos.mpr hr), ENNReal.ofReal_eq_zero, not_le, Ne]
      · simp only [ENNReal.ofReal_ne_top, Ne, not_false_iff]

instance (priority := 100) isUnifLocDoublingMeasureOfIsAddHaarMeasure :
    IsUnifLocDoublingMeasure μ := by
  refine ⟨⟨(2 : Real>=0) ^ finrank Real E, ?_⟩⟩
  filter_upwards [self_mem_nhdsWithin] with r hr x
  rw [addHaar_closedBall_mul μ x zero_le_two (le_of_lt hr)]; rw [addHaar_closedBall_center μ x]; rw [ENNReal.ofReal]; rw [Real.toNNReal_pow zero_le_two]
  simp only [Real.toNNReal_ofNat, le_refl]

section

/-!
### The Lebesgue measure associated to an alternating map
-/

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup G] [NormedSpace Real G]
  [MeasurableSpace G] [BorelSpace G]

/--
theorem `addHaar_parallelepiped` / 定理 `addHaar_parallelepiped`

English:
theorem addHaar_parallelepiped
  given: (b : Basis ι Real G) (v : ι -> G)
  proof: by
  have : FiniteDimensional Real G := b.finiteDimensional_of_finite
  have A : parallelepiped v = b.constr Nat v '' parallelepiped b := by
    rw [image_parallelepiped]
exact congr_arg _ funext fun i => (b.constr_basis Nat v i).symm
  rw [A]; rw [addHaar_image_linearMap]; rw [b.addHaar_self]; rw [

中文:
定理 addHaar_parallelepiped
  条件: (b : Basis ι 实数 G) (v : ι -> G)
  证明: by
  have : FiniteDimensional Real G := b.finiteDimensional_of_finite
  have A : parallelepiped v = b.constr Nat v '' parallelepiped b := by
    rw [image_parallelepiped]
exact congr_arg _ funext fun i => (b.constr_basis Nat v i).symm
  rw [A]; rw [addHaar_image_linearMap]; rw [b.addHaar_self]; rw [

Depends on / 依赖: Basis.det_apply, Basis.toMatrix_eq_toMatrix_constr, FiniteDimensional, LinearMap, LinearMap.det_toMatrix, addHaar_image_linearMap, addHaar_self, b.addHaar_self, b.constr, b.constr_basis, b.finiteDimensional_of_finite, congr_arg, constr, constr_basis, det_apply, det_toMatrix, finiteDimensional_of_finite, image_parallelepiped, mul_one, parallelepiped
-/
theorem addHaar_parallelepiped (b : Basis ι Real G) (v : ι -> G) :
    b.addHaar (parallelepiped v) = ENNReal.ofReal |b.det v| := by
  have : FiniteDimensional Real G := b.finiteDimensional_of_finite
  have A : parallelepiped v = b.constr Nat v '' parallelepiped b := by
    rw [image_parallelepiped]
exact congr_arg _ funext fun i => (b.constr_basis Nat v i).symm
  rw [A]; rw [addHaar_image_linearMap]; rw [b.addHaar_self]; rw [mul_one]; rw [← LinearMap.det_toMatrix b]; rw [← Basis.toMatrix_eq_toMatrix_constr]; rw [Basis.det_apply]

variable [FiniteDimensional Real G] {n : Nat} [_i : Fact (finrank Real G = n)]

/-- The Lebesgue measure associated to an alternating map. It gives measure `|ω v|` to the
parallelepiped spanned by the vectors `v₁, ..., vₙ`. Note that it is not always a Haar measure,
as it can be zero, but it is always locally finite and translation invariant. -/
noncomputable irreducible_def _root_.AlternatingMap.measure (ω : G [⋀^Fin n]->ₗ[Real] Real) :
    Measure G :=
  ‖ω (finBasisOfFinrankEq Real G _i.out)‖₊ • (finBasisOfFinrankEq Real G _i.out).addHaar

/--
theorem `_root_.AlternatingMap.measure_parallelepiped` / 定理 `_root_.AlternatingMap.measure_parallelepiped`

English:
theorem _root_.AlternatingMap.measure_parallelepiped
  statement: (ω : G [⋀^Fin n]->ₗ[Real] Real)
  proof: by
  conv_rhs => rw [ω.eq_smul_basis_det (finBasisOfFinrankEq Real G _i.out)]
  simp only [addHaar_parallelepiped, AlternatingMap.measure, coe_nnreal_smul_apply,
    AlternatingMap.smul_apply, smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    ← Real.enorm_eq_ofReal_abs, enorm]

中文:
定理 _root_.AlternatingMap.measure_parallelepiped
  结论: (ω : G [⋀^Fin n]->ₗ[实数] 实数)
  证明: by
  conv_rhs => rw [ω.eq_smul_basis_det (finBasisOfFinrankEq Real G _i.out)]
  simp only [addHaar_parallelepiped, AlternatingMap.measure, coe_nnreal_smul_apply,
    AlternatingMap.smul_apply, smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    ← Real.enorm_eq_ofReal_abs, enorm]

Depends on / 依赖: AlternatingMap, AlternatingMap.measure, AlternatingMap.smul_apply, ENNReal, ENNReal.ofReal_mul, Real.enorm_eq_ofReal_abs, _i.out, abs_mul, abs_nonneg, addHaar_parallelepiped, coe_nnreal_smul_apply, conv_rhs, enorm_eq_ofReal_abs, eq_smul_basis_det, finBasisOfFinrankEq, measure, ofReal_mul, smul_apply, smul_eq_mul
-/
theorem _root_.AlternatingMap.measure_parallelepiped (ω : G [⋀^Fin n]->ₗ[Real] Real)
    (v : Fin n -> G) : ω.measure (parallelepiped v) = ENNReal.ofReal |ω v| := by
  conv_rhs => rw [ω.eq_smul_basis_det (finBasisOfFinrankEq Real G _i.out)]
  simp only [addHaar_parallelepiped, AlternatingMap.measure, coe_nnreal_smul_apply,
    AlternatingMap.smul_apply, smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    ← Real.enorm_eq_ofReal_abs, enorm]

instance (ω : G [⋀^Fin n]->ₗ[Real] Real) : IsAddLeftInvariant ω.measure := by
  rw [AlternatingMap.measure]; infer_instance

instance (ω : G [⋀^Fin n]->ₗ[Real] Real) : IsLocallyFiniteMeasure ω.measure := by
  rw [AlternatingMap.measure]; infer_instance

end


/--
theorem `tendsto_addHaar_inter_smul_zero_of_density_zero_aux1` / 定理 `tendsto_addHaar_inter_smul_zero_of_density_zero_aux1`

English:
theorem tendsto_addHaar_inter_smul_zero_of_density_zero_aux1
  statement: (s : Set E) (x : E)
  proof: by
  have A : Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    apply
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
        (Eventually.of_forall fun b => zero_le)
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 

中文:
定理 tendsto_addHaar_inter_smul_zero_of_density_zero_aux1
  结论: (s : Set E) (x : E)
  证明: by
  have A : Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    apply
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
        (Eventually.of_forall fun b => zero_le)
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 

Depends on / 依赖: Eventually, Eventually.of_forall, Tendsto, affinity_unitClosedBall, closedBall, filter_upwards, of_forall, rpos.le, self_mem_nhdsWithin, singleton_vadd, t_bound, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, vadd_eq_add, zero_le
-/
theorem tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (u : Set E) (h'u : μ u != 0) (t_bound : t subseteq closedBall 0 1) :
    Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) := by
  have A : Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    apply
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
        (Eventually.of_forall fun b => zero_le)
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    grw [t_bound]
    rw [← vadd_eq_add]; rw [singleton_vadd]; rw [affinity_unitClosedBall rpos.le]
  have B :
    Tendsto (fun r : Real => μ (closedBall x r) / μ ({x} + r • u)) (𝓝[>] 0)
      (𝓝 (μ (closedBall x 1) / μ ({x} + u))) := by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    have : closedBall x r = {x} + r • closedBall (0 : E) 1 := by
      simp only [_root_.smul_closedBall, Real.norm_of_nonneg rpos.le, zero_le_one, add_zero,
        mul_one, singleton_add_closedBall, smul_zero]
    simp only [this, addHaar_singleton_add_smul_div_singleton_add_smul μ rpos.ne']
    simp only [addHaar_closedBall_center, image_add_left, measure_preimage_add, singleton_add]
  have C : Tendsto (fun r : Real =>
        μ (s inter ({x} + r • t)) / μ (closedBall x r) * (μ (closedBall x r) / μ ({x} + r • u)))
      (𝓝[>] 0) (𝓝 (0 * (μ (closedBall x 1) / μ ({x} + u)))) := by
    apply ENNReal.Tendsto.mul A _ B (Or.inr ENNReal.zero_ne_top)
    simp [ENNReal.div_eq_top, h'u, measure_closedBall_lt_top.ne]
  simp only [zero_mul] at C
  apply C.congr' _
  filter_upwards [self_mem_nhdsWithin]
  rintro r (rpos : 0 < r)
  calc μ (s inter ({x} + r • t)) / μ (closedBall x r) * (μ (closedBall x r) / μ ({x} + r • u))
    _ = μ (closedBall x r) * (μ (closedBall x r))⁻¹ *
        (μ (s inter ({x} + r • t)) / μ ({x} + r • u)) := by simp only [div_eq_mul_inv]; ring
    _ = μ (s inter ({x} + r • t)) / μ ({x} + r • u) := by
      rw [ENNReal.mul_inv_cancel (measure_closedBall_pos μ x rpos).ne'
          measure_closedBall_lt_top.ne]; rw [one_mul]

/--
theorem `tendsto_addHaar_inter_smul_zero_of_density_zero_aux2` / 定理 `tendsto_addHaar_inter_smul_zero_of_density_zero_aux2`

English:
theorem tendsto_addHaar_inter_smul_zero_of_density_zero_aux2
  statement: (s : Set E) (x : E)
  proof: by
  set t' := R⁻¹ • t with ht'
  set u' := R⁻¹ • u with hu'
  have A : Tendsto (fun r : Real => μ (s inter ({x} + r • t')) / μ ({x} + r • u')) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 μ s x h t' u'
    · simp only [u', h'u, (pow_pos Rpos _).ne', abs_nonpos

中文:
定理 tendsto_addHaar_inter_smul_zero_of_density_zero_aux2
  结论: (s : Set E) (x : E)
  证明: by
  set t' := R⁻¹ • t with ht'
  set u' := R⁻¹ • u with hu'
  have A : Tendsto (fun r : Real => μ (s inter ({x} + r • t')) / μ ({x} + r • u')) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 μ s x h t' u'
    · simp only [u', h'u, (pow_pos Rpos _).ne', abs_nonpos

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, Rpos.le, Tendsto, abs_nonpos_iff, addHaar_smul, inv_eq_zero, inv_pow, mul_eq_zero, not_false_iff, ofReal_eq_zero, or_self_iff, pow_pos, smul_closedBall, smul_set_mono, smul_zero, t_bound, tendsto_addHaar_inter_smul_zero_of_density_zero_aux1, trans_eq
-/
theorem tendsto_addHaar_inter_smul_zero_of_density_zero_aux2 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (u : Set E) (h'u : μ u != 0) (R : Real) (Rpos : 0 < R) (t_bound : t subseteq closedBall 0 R) :
    Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) := by
  set t' := R⁻¹ • t with ht'
  set u' := R⁻¹ • u with hu'
  have A : Tendsto (fun r : Real => μ (s inter ({x} + r • t')) / μ ({x} + r • u')) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 μ s x h t' u'
    · simp only [u', h'u, (pow_pos Rpos _).ne', abs_nonpos_iff, addHaar_smul, not_false_iff,
        ENNReal.ofReal_eq_zero, inv_eq_zero, inv_pow, Ne, or_self_iff, mul_eq_zero]
    · refine (smul_set_mono t_bound).trans_eq ?_
      rw [smul_closedBall _ _ Rpos.le]; rw [smul_zero]; rw [Real.norm_of_nonneg (inv_nonneg.2 Rpos.le)]; rw [inv_mul_cancel₀ Rpos.ne']
  have B : Tendsto (fun r : Real => R * r) (𝓝[>] 0) (𝓝[>] (R * 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (tendsto_const_nhds.mul tendsto_id).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin]
      intro r rpos
      rw [mul_zero]
      exact mul_pos Rpos rpos
  rw [mul_zero] at B
  apply (A.comp B).congr' _
  filter_upwards [self_mem_nhdsWithin]
  rintro r -
  have T : (R * r) • t' = r • t := by
    rw [mul_comm]; rw [ht']; rw [smul_smul]; rw [mul_assoc]; rw [mul_inv_cancel₀ Rpos.ne']; rw [mul_one]
  have U : (R * r) • u' = r • u := by
    rw [mul_comm]; rw [hu']; rw [smul_smul]; rw [mul_assoc]; rw [mul_inv_cancel₀ Rpos.ne']; rw [mul_one]
  dsimp
  rw [T]; rw [U]

/--
theorem `tendsto_addHaar_inter_smul_zero_of_density_zero` / 定理 `tendsto_addHaar_inter_smul_zero_of_density_zero`

English:
theorem tendsto_addHaar_inter_smul_zero_of_density_zero
  statement: (s : Set E) (x : E)
  proof: by
  refine tendsto_order.2 ⟨fun a' ha' => (ENNReal.not_lt_zero ha').elim, fun ε (εpos : 0 < ε) => ?_⟩
  rcases eq_or_ne (μ t) 0 with (h't | h't)
  · filter_upwards with r
    suffices H : μ (s inter ({x} + r • t)) = 0 by
      rw [H]; simpa only [ENNReal.zero_div] using εpos
    rw [← nonpos_iff_eq

中文:
定理 tendsto_addHaar_inter_smul_zero_of_density_zero
  结论: (s : Set E) (x : E)
  证明: by
  refine tendsto_order.2 ⟨fun a' ha' => (ENNReal.not_lt_zero ha').elim, fun ε (εpos : 0 < ε) => ?_⟩
  rcases eq_or_ne (μ t) 0 with (h't | h't)
  · filter_upwards with r
    suffices H : μ (s inter ({x} + r • t)) = 0 by
      rw [H]; simpa only [ENNReal.zero_div] using εpos
    rw [← nonpos_iff_eq

Depends on / 依赖: ENNReal, ENNReal.not_lt_zero, ENNReal.zero_div, addHaar_smul, eq_or_ne, filter_upwards, image_add_left, inter_subset_right, measure_mono, measure_preimage_add, mul_zero, nonpos_iff_eq_zero, not_lt_zero, singleton_add, tendsto_order, zero_div
-/
theorem tendsto_addHaar_inter_smul_zero_of_density_zero (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (ht : MeasurableSet t) (h''t : μ t != ∞) :
    Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a' ha' => (ENNReal.not_lt_zero ha').elim, fun ε (εpos : 0 < ε) => ?_⟩
  rcases eq_or_ne (μ t) 0 with (h't | h't)
  · filter_upwards with r
    suffices H : μ (s inter ({x} + r • t)) = 0 by
      rw [H]; simpa only [ENNReal.zero_div] using εpos
    rw [← nonpos_iff_eq_zero]
    calc
      μ (s inter ({x} + r • t)) <= μ ({x} + r • t) := measure_mono inter_subset_right
      _ = 0 := by
        simp only [h't, addHaar_smul, image_add_left, measure_preimage_add, singleton_add,
          mul_zero]
  obtain ⟨n, npos, hn⟩ : exists n : Nat, 0 < n ∧ μ (t \ closedBall 0 n) < ε / 2 * μ t := by
    have A :
      Tendsto (fun n : Nat => μ (t \ closedBall 0 n)) atTop
        (𝓝 (μ (⋂ n : Nat, t \ closedBall 0 n))) := by
      have N : exists n : Nat, μ (t \ closedBall 0 n) != ∞ :=
        ⟨0, ((measure_mono sdiff_subset).trans_lt h''t.lt_top).ne⟩
      refine tendsto_measure_iInter_atTop
        (fun n => (ht.diff measurableSet_closedBall).nullMeasurableSet) (fun m n hmn => ?_) N
      exact sdiff_subset_sdiff Subset.rfl (by gcongr)
    have : ⋂ n : Nat, t \ closedBall 0 n = ∅ := by
      simp_rw [sdiff_eq, ← inter_iInter, iInter_eq_compl_iUnion_compl, compl_compl,
        iUnion_closedBall_nat, compl_univ, inter_empty]
    simp only [this, measure_empty] at A
    have I : 0 < ε / 2 * μ t := ENNReal.mul_pos (ENNReal.half_pos εpos.ne').ne' h't
    exact (Eventually.and (Ioi_mem_atTop 0) ((tendsto_order.1 A).2 _ I)).exists
  have L :
    Tendsto (fun r : Real => μ (s inter ({x} + r • (t inter closedBall 0 n))) / μ ({x} + r • t)) (𝓝[>] 0)
      (𝓝 0) :=
    tendsto_addHaar_inter_smul_zero_of_density_zero_aux2 μ s x h _ t h't n (Nat.cast_pos.2 npos)
      inter_subset_right
  filter_upwards [(tendsto_order.1 L).2 _ (ENNReal.half_pos εpos.ne'), self_mem_nhdsWithin]
  rintro r hr (rpos : 0 < r)
  have I :
    μ (s inter ({x} + r • t)) <=
      μ (s inter ({x} + r • (t inter closedBall 0 n))) + μ ({x} + r • (t \ closedBall 0 n)) :=
    calc
      μ (s inter ({x} + r • t)) =
          μ (s inter ({x} + r • (t inter closedBall 0 n)) union s inter ({x} + r • (t \ closedBall 0 n))) := by
        rw [← inter_union_distrib_left]; rw [← add_union]; rw [← smul_set_union]; rw [inter_union_sdiff]
      _ <= μ (s inter ({x} + r • (t inter closedBall 0 n))) + μ (s inter ({x} + r • (t \ closedBall 0 n))) :=
        measure_union_le _ _
      _ <= μ (s inter ({x} + r • (t inter closedBall 0 n))) + μ ({x} + r • (t \ closedBall 0 n)) := by
        gcongr; apply inter_subset_right
  calc
    μ (s inter ({x} + r • t)) / μ ({x} + r • t) <=
        (μ (s inter ({x} + r • (t inter closedBall 0 n))) + μ ({x} + r • (t \ closedBall 0 n))) /
          μ ({x} + r • t) := by gcongr
    _ < ε / 2 + ε / 2 := by
      rw [ENNReal.add_div]
      apply ENNReal.add_lt_add hr _
      rwa [addHaar_singleton_add_smul_div_singleton_add_smul μ rpos.ne',
        ENNReal.div_lt_iff (Or.inl h't) (Or.inl h''t)]
    _ = ε := ENNReal.add_halves _

/--
theorem `tendsto_addHaar_inter_smul_one_of_density_one_aux` / 定理 `tendsto_addHaar_inter_smul_one_of_density_one_aux`

English:
theorem tendsto_addHaar_inter_smul_one_of_density_one_aux
  statement: (s : Set E) (hs : MeasurableSet s)
  proof: by
  have I : forall u v, μ u != 0 -> μ u != ∞ -> MeasurableSet v ->
    μ u / μ u - μ (vᶜ inter u) / μ u = μ (v inter u) / μ u := by
    intro u v uzero utop vmeas
    simp_rw [div_eq_mul_inv]
    rw [← ENNReal.sub_mul]; swap
    · simp only [uzero, ENNReal.inv_eq_top, imp_true_iff, Ne, not_false_i

中文:
定理 tendsto_addHaar_inter_smul_one_of_density_one_aux
  结论: (s : Set E) (hs : MeasurableSet s)
  证明: by
  have I : forall u v, μ u != 0 -> μ u != ∞ -> MeasurableSet v ->
    μ u / μ u - μ (vᶜ inter u) / μ u = μ (v inter u) / μ u := by
    intro u v uzero utop vmeas
    simp_rw [div_eq_mul_inv]
    rw [← ENNReal.sub_mul]; swap
    · simp only [uzero, ENNReal.inv_eq_top, imp_true_iff, Ne, not_false_i

Depends on / 依赖: ENNReal, ENNReal.eq_sub_of_add_eq, ENNReal.inv_eq_top, ENNReal.sub_mul, MeasurableSet, Tendsto, closedBall, div_eq_mul_inv, eq_comm, eq_sub_of_add_eq, imp_true_iff, inter_comm, inv_eq_top, measure_inter_add_sdiff, not_false_iff, simp_rw, sub_mul
-/
theorem tendsto_addHaar_inter_smul_one_of_density_one_aux (s : Set E) (hs : MeasurableSet s)
    (x : E) (h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1))
    (t : Set E) (ht : MeasurableSet t) (h't : μ t != 0) (h''t : μ t != ∞) :
    Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
  have I : forall u v, μ u != 0 -> μ u != ∞ -> MeasurableSet v ->
    μ u / μ u - μ (vᶜ inter u) / μ u = μ (v inter u) / μ u := by
    intro u v uzero utop vmeas
    simp_rw [div_eq_mul_inv]
    rw [← ENNReal.sub_mul]; swap
    · simp only [uzero, ENNReal.inv_eq_top, imp_true_iff, Ne, not_false_iff]
    congr 1
    rw [inter_comm _ u]; rw [inter_comm _ u]; rw [eq_comm]
    exact ENNReal.eq_sub_of_add_eq' utop (measure_inter_add_sdiff u vmeas)
  have L : Tendsto (fun r => μ (sᶜ inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    have A : Tendsto (fun r => μ (closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_const_nhds.congr' _
      filter_upwards [self_mem_nhdsWithin]
      intro r hr
      rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_cancel]
      · exact (measure_closedBall_pos μ _ hr).ne'
      · exact measure_closedBall_lt_top.ne
    have B := ENNReal.Tendsto.sub A h (Or.inl ENNReal.one_ne_top)
    simp only [tsub_self] at B
    apply B.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    convert!
      I (closedBall x r) sᶜ (measure_closedBall_pos μ _ rpos).ne' measure_closedBall_lt_top.ne
        hs.compl
    rw [compl_compl]
  have L' : Tendsto (fun r : Real => μ (sᶜ inter ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_addHaar_inter_smul_zero_of_density_zero μ sᶜ x L t ht h''t
  have L'' : Tendsto (fun r : Real => μ ({x} + r • t) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    rw [addHaar_singleton_add_smul_div_singleton_add_smul μ rpos.ne']; rw [ENNReal.div_self h't h''t]
  have := ENNReal.Tendsto.sub L'' L' (Or.inl ENNReal.one_ne_top)
  simp only [tsub_zero] at this
  apply this.congr' _
  filter_upwards [self_mem_nhdsWithin]
  rintro r (rpos : 0 < r)
  refine I ({x} + r • t) s ?_ ?_ hs
  · simp only [h't, abs_of_nonneg rpos.le, pow_pos rpos, addHaar_smul, image_add_left,
      ENNReal.ofReal_eq_zero, not_le, or_false, Ne, measure_preimage_add, abs_pow,
      singleton_add, mul_eq_zero]
  · simp [h''t, ENNReal.ofReal_ne_top, addHaar_smul, image_add_left, ENNReal.mul_eq_top,
      Ne, measure_preimage_add, singleton_add]

/--
theorem `tendsto_addHaar_inter_smul_one_of_density_one` / 定理 `tendsto_addHaar_inter_smul_one_of_density_one`

English:
theorem tendsto_addHaar_inter_smul_one_of_density_one
  statement: (s : Set E) (x : E)
  proof: by
  have : Tendsto (fun r : Real => μ (toMeasurable μ s inter ({x} + r • t)) / μ ({x} + r • t))
    (𝓝[>] 0) (𝓝 1) := by
    apply
      tendsto_addHaar_inter_smul_one_of_density_one_aux μ _ (measurableSet_toMeasurable _ _) _ _
        t ht h't h''t
    apply tendsto_of_tendsto_of_tendsto_of_le_of_

中文:
定理 tendsto_addHaar_inter_smul_one_of_density_one
  结论: (s : Set E) (x : E)
  证明: by
  have : Tendsto (fun r : Real => μ (toMeasurable μ s inter ({x} + r • t)) / μ ({x} + r • t))
    (𝓝[>] 0) (𝓝 1) := by
    apply
      tendsto_addHaar_inter_smul_one_of_density_one_aux μ _ (measurableSet_toMeasurable _ _) _ _
        t ht h't h''t
    apply tendsto_of_tendsto_of_tendsto_of_le_of_

Depends on / 依赖: ENNReal, ENNReal.div_le_of_le_mul, Eventually, Eventually.of_forall, Tendsto, div_le_of_le_mul, filter_upwards, inter_subset_ri, measurableSet_toMeasurable, measure_mono, of_forall, one_mul, self_mem_nhdsWithin, subset_toMeasurable, tendsto_addHaar_inter_smul_one_of_density_one_aux, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, toMeasurable
-/
theorem tendsto_addHaar_inter_smul_one_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t != 0) (h''t : μ t != ∞) :
    Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
  have : Tendsto (fun r : Real => μ (toMeasurable μ s inter ({x} + r • t)) / μ ({x} + r • t))
    (𝓝[>] 0) (𝓝 1) := by
    apply
      tendsto_addHaar_inter_smul_one_of_density_one_aux μ _ (measurableSet_toMeasurable _ _) _ _
        t ht h't h''t
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h tendsto_const_nhds
    · refine Eventually.of_forall fun r => ?_
      gcongr
      apply subset_toMeasurable
    · filter_upwards [self_mem_nhdsWithin]
      rintro r -
      apply ENNReal.div_le_of_le_mul
      rw [one_mul]
      exact measure_mono inter_subset_right
  refine this.congr fun r => ?_
  congr 1
  apply measure_toMeasurable_inter_of_sFinite
  simp only [image_add_left, singleton_add]
  apply (continuous_const_add (-x)).measurable (ht.const_smul₀ r)

/--
theorem `eventually_nonempty_inter_smul_of_density_one` / 定理 `eventually_nonempty_inter_smul_of_density_one`

English:
theorem eventually_nonempty_inter_smul_of_density_one
  statement: (s : Set E) (x : E)
  proof: by
  obtain ⟨t', t'_meas, t't, t'pos, t'top⟩ : exists t', MeasurableSet t' ∧ t' subseteq t ∧ 0 < μ t' ∧ μ t' < ⊤ :=
    exists_subset_measure_lt_top ht h't.bot_lt
  filter_upwards [(tendsto_order.1
          (tendsto_addHaar_inter_smul_one_of_density_one μ s x h t' t'_meas t'pos.ne' t'top.ne)).1
   

中文:
定理 eventually_nonempty_inter_smul_of_density_one
  结论: (s : Set E) (x : E)
  证明: by
  obtain ⟨t', t'_meas, t't, t'pos, t'top⟩ : exists t', MeasurableSet t' ∧ t' subseteq t ∧ 0 < μ t' ∧ μ t' < ⊤ :=
    exists_subset_measure_lt_top ht h't.bot_lt
  filter_upwards [(tendsto_order.1
          (tendsto_addHaar_inter_smul_one_of_density_one μ s x h t' t'_meas t'pos.ne' t'top.ne)).1
   

Depends on / 依赖: ENNReal, ENNReal.not_lt_zero, ENNReal.zero_div, MeasurableSet, Nonempty, _meas, bot_lt, exists_subset_measure_lt_top, filter_upwards, nonempty_of_measure_ne_zero, not_lt_zero, pos.ne, subseteq, t.bot_lt, tendsto_addHaar_inter_smul_one_of_density_one, tendsto_order, top.ne, zero_div, zero_lt_one
-/
theorem eventually_nonempty_inter_smul_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t != 0) :
    forallᶠ r in 𝓝[>] (0 : Real), (s inter ({x} + r • t)).Nonempty := by
  obtain ⟨t', t'_meas, t't, t'pos, t'top⟩ : exists t', MeasurableSet t' ∧ t' subseteq t ∧ 0 < μ t' ∧ μ t' < ⊤ :=
    exists_subset_measure_lt_top ht h't.bot_lt
  filter_upwards [(tendsto_order.1
          (tendsto_addHaar_inter_smul_one_of_density_one μ s x h t' t'_meas t'pos.ne' t'top.ne)).1
      0 zero_lt_one]
  intro r hr
  have : μ (s inter ({x} + r • t')) != 0 := fun h' => by
    simp only [ENNReal.not_lt_zero, ENNReal.zero_div, h'] at hr
  have : (s inter ({x} + r • t')).Nonempty := nonempty_of_measure_ne_zero this
  apply this.mono (inter_subset_inter Subset.rfl _)
  exact add_subset_add Subset.rfl (smul_set_mono t't)

end Measure

end MeasureTheory
