/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Doubling

/-!
# The product measure

In this file we define and prove properties about the binary product measure. If `α` and `β` have
s-finite measures `μ` resp. `ν` then `α × β` can be equipped with an s-finite measure `μ.prod ν`
that satisfies `(μ.prod ν) s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`.
We also have `(μ.prod ν) (s ×ˢ t) = μ s * ν t`, i.e. the measure of a rectangle is the product of
the measures of the sides.

We also prove Tonelli's theorem.

## Main definition

* `MeasureTheory.Measure.prod`: The product of two measures.

## Main results

* `MeasureTheory.Measure.prod_apply` states `μ.prod ν s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`
  for measurable `s`. `MeasureTheory.Measure.prod_apply_symm` is the reversed version.
* `MeasureTheory.Measure.prod_prod` states `μ.prod ν (s ×ˢ t) = μ s * ν t` for measurable sets
  `s` and `t`.
* `MeasureTheory.lintegral_prod`: Tonelli's theorem. It states that for a measurable function
  `α × β → ℝ≥0∞` we have `∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ`. The version
  for functions `α → β → ℝ≥0∞` is reversed, and called `lintegral_lintegral`. Both versions have
  a variant with `_symm` appended, where the order of integration is reversed.
  The lemma `Measurable.lintegral_prod_right'` states that the inner integral of the right-hand side
  is measurable.

## Implementation Notes

Many results are proven twice, once for functions in curried form (`α → β → γ`) and one for
functions in uncurried form (`α × β → γ`). The former often has an assumption
`Measurable (uncurry f)`, which could be inconvenient to discharge, but for the latter it is more
common that the function has to be given explicitly, since Lean cannot synthesize the function by
itself. We name the lemmas about the uncurried form with a prime.
Tonelli's theorem has a different naming scheme, since the version for the uncurried version is
reversed.

## Tags

product measure, Tonelli's theorem, Fubini-Tonelli theorem
-/

@[expose] public section


noncomputable section

open Topology ENNReal MeasureTheory Set Function Real ENNReal MeasurableSpace MeasureTheory.Measure

open TopologicalSpace hiding generateFrom

open Filter hiding prod_eq map

variable {α β γ : Type*}

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {μ μ' : Measure α} {ν ν' : Measure β} {τ : Measure γ}

/--
theorem `measurable_measure_prodMk_left_finite` / 定理 `measurable_measure_prodMk_left_finite`

English:
theorem measurable_measure_prodMk_left_finite
  statement: [IsFiniteMeasure ν] {s : Set (α × β)}
  proof: by
  induction s, hs using induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical simpa only [mk_preimage_prod_right_eq_if, measure_if]
      using measurable_const.indicator hs
  | compl s hs ihs =>
    si

中文:
定理 measurable_measure_prodMk_left_finite
  结论: [是有限测度 ν] {s : 集合 (α × β)}
  证明: by
  induction s, hs using induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical simpa only [mk_preimage_prod_right_eq_if, measure_if]
      using measurable_const.indicator hs
  | compl s hs ihs =>
    si

Depends on / 依赖: Prod.mk, classical, const_sub, generateFrom_prod, generateFrom_prod.symm, iUnion, ihs.const_sub, indicator, induction_on_inter, isPiSystem_prod, measurable_const, measurable_const.indicator, measurable_prodMk_left, measure_compl, measure_if, measure_ne_top, mk_preimage_prod_right_eq_if, preimage_, preimage_compl, simp_rw
-/
theorem measurable_measure_prodMk_left_finite [IsFiniteMeasure ν] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻¹' s) := by
  induction s, hs using induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical simpa only [mk_preimage_prod_right_eq_if, measure_if]
      using measurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, measure_compl (measurable_prodMk_left hs) (measure_ne_top ν _)]
    exact ihs.const_sub _
  | iUnion f hfd hfm ihf =>
    have (a : α) : ν (Prod.mk a ⁻¹' ⋃ i, f i) = ∑' i, ν (Prod.mk a ⁻¹' f i) := by
      rw [preimage_iUnion]; rw [measure_iUnion]
      exacts [hfd.mono fun _ _ => .preimage _, fun i => measurable_prodMk_left (hfm i)]
    simpa only [this] using Measurable.tsum ihf

/--
theorem `measurable_measure_prodMk_left` / 定理 `measurable_measure_prodMk_left`

English:
theorem measurable_measure_prodMk_left
  given: [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s)
  proof: by
  rw [← sum_sfiniteSeq ν]
  simp_rw [Measure.sum_apply_of_countable]
  exact Measurable.tsum (fun i => measurable_measure_prodMk_left_finite hs)

中文:
定理 measurable_measure_prodMk_left
  条件: [SFinite ν] {s : 集合 (α × β)} (hs : 可测集 s)
  证明: by
  rw [← sum_sfiniteSeq ν]
  simp_rw [Measure.sum_apply_of_countable]
  exact Measurable.tsum (fun i => measurable_measure_prodMk_left_finite hs)

Depends on / 依赖: Measurable, Measurable.tsum, Measure, Measure.sum_apply_of_countable, measurable_measure_prodMk_left_finite, simp_rw, sum_apply_of_countable, sum_sfiniteSeq
-/
theorem measurable_measure_prodMk_left [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun x => ν (Prod.mk x ⁻¹' s) := by
  rw [← sum_sfiniteSeq ν]
  simp_rw [Measure.sum_apply_of_countable]
  exact Measurable.tsum (fun i => measurable_measure_prodMk_left_finite hs)

/--
theorem `measurable_measure_prodMk_right` / 定理 `measurable_measure_prodMk_right`

English:
theorem measurable_measure_prodMk_right
  statement: {μ : Measure α} [SFinite μ] {s : Set (α × β)}
  proof: measurable_measure_prodMk_left (measurableSet_swap_iff.mpr hs)

中文:
定理 measurable_measure_prodMk_right
  结论: {μ : 测度 α} [SFinite μ] {s : 集合 (α × β)}
  证明: measurable_measure_prodMk_left (measurableSet_swap_iff.mpr hs)

Depends on / 依赖: measurableSet_swap_iff, measurableSet_swap_iff.mpr, measurable_measure_prodMk_left
-/
theorem measurable_measure_prodMk_right {μ : Measure α} [SFinite μ] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun y => μ ((fun x => (x, y)) ⁻¹' s) :=
  measurable_measure_prodMk_left (measurableSet_swap_iff.mpr hs)

/--
theorem `Measurable.map_prodMk_left` / 定理 `Measurable.map_prodMk_left`

English:
theorem Measurable.map_prodMk_left
  given: [SFinite ν]
  proof: by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prodMk_left hs]
  exact measurable_measure_prodMk_left hs

中文:
定理 可测.map_prodMk_left
  条件: [SFinite ν]
  证明: by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prodMk_left hs]
  exact measurable_measure_prodMk_left hs

Depends on / 依赖: map_apply, measurable_measure_prodMk_left, measurable_of_measurable_coe, measurable_prodMk_left, simp_rw
-/
theorem Measurable.map_prodMk_left [SFinite ν] :
    Measurable fun x : α => map (Prod.mk x) ν := by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prodMk_left hs]
  exact measurable_measure_prodMk_left hs

/--
theorem `Measurable.map_prodMk_right` / 定理 `Measurable.map_prodMk_right`

English:
theorem Measurable.map_prodMk_right
  given: {μ : Measure α} [SFinite μ]
  proof: by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prodMk_right hs]
  exact measurable_measure_prodMk_right hs

中文:
定理 可测.map_prodMk_right
  条件: {μ : 测度 α} [SFinite μ]
  证明: by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prodMk_right hs]
  exact measurable_measure_prodMk_right hs

Depends on / 依赖: map_apply, measurable_measure_prodMk_right, measurable_of_measurable_coe, measurable_prodMk_right, simp_rw
-/
theorem Measurable.map_prodMk_right {μ : Measure α} [SFinite μ] :
    Measurable fun y : β => map (fun x : α => (x, y)) μ := by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prodMk_right hs]
  exact measurable_measure_prodMk_right hs

/--
theorem `Measurable.lintegral_prod_right'` / 定理 `Measurable.lintegral_prod_right'`

English:
theorem Measurable.lintegral_prod_right'
  given: [SFinite ν]
  proof: by
  have m := @measurable_prodMk_left
  refine Measurable.ennreal_induction (motive := fun f => Measurable fun (x : α) => ∫⁻ y, f (x, y) ∂ν)
    ?_ ?_ ?_
  · intro c s hs
    simp only [← indicator_comp_right]
    suffices Measurable fun x => c * ν (Prod.mk x ⁻¹' s) by simpa [lintegral_indicator (m

中文:
定理 可测.lintegral_prod_right'
  条件: [SFinite ν]
  证明: by
  have m := @measurable_prodMk_left
  refine Measurable.ennreal_induction (motive := fun f => Measurable fun (x : α) => ∫⁻ y, f (x, y) ∂ν)
    ?_ ?_ ?_
  · intro c s hs
    simp only [← indicator_comp_right]
    suffices Measurable fun x => c * ν (Prod.mk x ⁻¹' s) by simpa [lintegral_indicator (m

Depends on / 依赖: Measurable, Measurable.ennreal_induction, Pi.add_apply, Prod.mk, add_apply, const_mul, ennreal_induction, h2f.add, hf.comp, indicator_comp_right, lintegral_add_left, lintegral_indicator, measurable_measure_prodMk_left, measurable_prodMk_left, motive
-/
theorem Measurable.lintegral_prod_right' [SFinite ν] :
    forall {f : α × β -> Real>=0∞}, Measurable f -> Measurable fun x => ∫⁻ y, f (x, y) ∂ν := by
  have m := @measurable_prodMk_left
  refine Measurable.ennreal_induction (motive := fun f => Measurable fun (x : α) => ∫⁻ y, f (x, y) ∂ν)
    ?_ ?_ ?_
  · intro c s hs
    simp only [← indicator_comp_right]
    suffices Measurable fun x => c * ν (Prod.mk x ⁻¹' s) by simpa [lintegral_indicator (m hs)]
    exact (measurable_measure_prodMk_left hs).const_mul _
  · rintro f g - hf - h2f h2g
    simp only [Pi.add_apply]
    conv => enter [1, x]; erw [lintegral_add_left (hf.comp m)]
    exact h2f.add h2g
  · intro f hf h2f h3f
    have : forall x, Monotone fun n y => f n (x, y) := fun x i j hij y => h2f hij (x, y)
    conv => enter [1, x]; erw [lintegral_iSup (fun n => (hf n).comp m) (this x)]
    exact .iSup h3f

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
@[fun_prop]
/--
theorem `Measurable.lintegral_prod_right` / 定理 `Measurable.lintegral_prod_right`

English:
theorem Measurable.lintegral_prod_right
  statement: [SFinite ν] {f : α -> β -> Real>=0∞}
  proof: hf.lintegral_prod_right'

中文:
定理 可测.lintegral_prod_right
  结论: [SFinite ν] {f : α -> β -> 实数>=0∞}
  证明: hf.lintegral_prod_right'

Depends on / 依赖: hf.lintegral_prod_right, lintegral_prod_right
-/
theorem Measurable.lintegral_prod_right [SFinite ν] {f : α -> β -> Real>=0∞}
    (hf : Measurable (uncurry f)) : Measurable fun x => ∫⁻ y, f x y ∂ν :=
  hf.lintegral_prod_right'

/--
theorem `Measurable.lintegral_prod_left'` / 定理 `Measurable.lintegral_prod_left'`

English:
theorem Measurable.lintegral_prod_left'
  given: [SFinite μ] {f : α × β -> Real>=0∞} (hf : Measurable f)
  proof: (measurable_swap_iff.mpr hf).lintegral_prod_right'

中文:
定理 可测.lintegral_prod_left'
  条件: [SFinite μ] {f : α × β -> 实数>=0∞} (hf : 可测 f)
  证明: (measurable_swap_iff.mpr hf).lintegral_prod_right'

Depends on / 依赖: lintegral_prod_right, measurable_swap_iff, measurable_swap_iff.mpr
-/
theorem Measurable.lintegral_prod_left' [SFinite μ] {f : α × β -> Real>=0∞} (hf : Measurable f) :
    Measurable fun y => ∫⁻ x, f (x, y) ∂μ :=
  (measurable_swap_iff.mpr hf).lintegral_prod_right'

/--
theorem `Measurable.lintegral_prod_left` / 定理 `Measurable.lintegral_prod_left`

English:
theorem Measurable.lintegral_prod_left
  statement: [SFinite μ] {f : α -> β -> Real>=0∞}
  proof: hf.lintegral_prod_left'

中文:
定理 可测.lintegral_prod_left
  结论: [SFinite μ] {f : α -> β -> 实数>=0∞}
  证明: hf.lintegral_prod_left'

Depends on / 依赖: hf.lintegral_prod_left, lintegral_prod_left
-/
theorem Measurable.lintegral_prod_left [SFinite μ] {f : α -> β -> Real>=0∞}
    (hf : Measurable (uncurry f)) : Measurable fun y => ∫⁻ x, f x y ∂μ :=
  hf.lintegral_prod_left'

/-! ### The product measure -/


namespace MeasureTheory

namespace Measure

/-- The binary product of measures. They are defined for arbitrary measures, but we basically
  prove all properties under the assumption that at least one of them is s-finite. -/
protected irreducible_def prod (μ : Measure α) (ν : Measure β) : Measure (α × β) :=
  bind μ fun x : α => map (Prod.mk x) ν

/--
Instance `prod.measureSpace` / 实例 `prod.measureSpace`

English:
instance prod.measureSpace
  signature: {α β} [MeasureSpace α] [MeasureSpace β]
  body: volume.prod volume

中文:
实例 乘积.measureSpace
  签名: {α β} [测度空间 α] [测度空间 β]
  定义体: volume.prod volume

Depends on / 依赖: volume, volume.prod
-/
instance prod.measureSpace {α β} [MeasureSpace α] [MeasureSpace β] : MeasureSpace (α × β) where
  volume := volume.prod volume

/--
theorem `volume_eq_prod` / 定理 `volume_eq_prod`

English:
theorem volume_eq_prod
  given: (α β) [MeasureSpace α] [MeasureSpace β]
  proof: rfl

中文:
定理 volume_eq_prod
  条件: (α β) [测度空间 α] [测度空间 β]
  证明: rfl
-/
theorem volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] :
    (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) :=
  rfl

/--
theorem `prod_apply_le` / 定理 `prod_apply_le`

English:
theorem prod_apply_le
  given: {s : Set (α × β)} (hs : MeasurableSet s)
  proof: by
  simp only [Measure.prod, ← map_apply measurable_prodMk_left hs]
  exact bind_apply_le _ hs

中文:
定理 prod_apply_le
  条件: {s : 集合 (α × β)} (hs : 可测集 s)
  证明: by
  simp only [Measure.prod, ← map_apply measurable_prodMk_left hs]
  exact bind_apply_le _ hs

Depends on / 依赖: Measure, Measure.prod, bind_apply_le, map_apply, measurable_prodMk_left
-/
theorem prod_apply_le {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  simp only [Measure.prod, ← map_apply measurable_prodMk_left hs]
  exact bind_apply_le _ hs

/--
theorem `prod_prod_le` / 定理 `prod_prod_le`

English:
theorem prod_prod_le
  given: (s : Set α) (t : Set β)
  statement: μ.prod ν (s ×ˢ t) <= μ s * ν t
  proof: by
  set S := toMeasurable μ s
  set T := toMeasurable ν t
  calc
    μ.prod ν (s ×ˢ t) <= μ.prod ν (S ×ˢ T) := by gcongr <;> apply subset_toMeasurable
    _ <= ∫⁻ x, ν (Prod.mk x ⁻¹' (S ×ˢ T)) ∂μ := prod_apply_le (by measurability)
    _ = μ S * ν T := by
      classical
      simp_rw [S, mk_preima

中文:
定理 prod_prod_le
  条件: (s : 集合 α) (t : 集合 β)
  结论: μ.乘积 ν (s ×ˢ t) <= μ s * ν t
  证明: by
  set S := toMeasurable μ s
  set T := toMeasurable ν t
  calc
    μ.prod ν (s ×ˢ t) <= μ.prod ν (S ×ˢ T) := by gcongr <;> apply subset_toMeasurable
    _ <= ∫⁻ x, ν (Prod.mk x ⁻¹' (S ×ˢ T)) ∂μ := prod_apply_le (by measurability)
    _ = μ S * ν T := by
      classical
      simp_rw [S, mk_preima

Depends on / 依赖: Prod.mk, classical, lintegral_const, lintegral_indicator, measurability, measurableSet_toMeasurable, measure_if, measure_toMeasurable, mk_preimage_prod_right_eq_if, mul_comm, prod_apply_le, restrict_apply_univ, simp_rw, subset_toMeasurable, toMeasurable
-/
theorem prod_prod_le (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) <= μ s * ν t := by
  set S := toMeasurable μ s
  set T := toMeasurable ν t
  calc
    μ.prod ν (s ×ˢ t) <= μ.prod ν (S ×ˢ T) := by gcongr <;> apply subset_toMeasurable
    _ <= ∫⁻ x, ν (Prod.mk x ⁻¹' (S ×ˢ T)) ∂μ := prod_apply_le (by measurability)
    _ = μ S * ν T := by
      classical
      simp_rw [S, mk_preimage_prod_right_eq_if, measure_if,
        lintegral_indicator (measurableSet_toMeasurable _ _), lintegral_const,
        restrict_apply_univ, mul_comm]
    _ = μ s * ν t := by rw [measure_toMeasurable, measure_toMeasurable]

/--
Instance `prod.instNullSingletonClass_fst` / 实例 `prod.instNullSingletonClass_fst`

English:
instance prod.instNullSingletonClass_fst
  signature: [NullSingletonClass μ]
  body: by rw [singleton_prod_singleton]
    _ <= μ {x} * ν {y} := prod_prod_le _ _
    _ = 0 := by simp

中文:
实例 乘积.instNullSingletonClass_fst
  签名: [NullSingleton类 μ]
  定义体: by rw [singleton_prod_singleton]
    _ <= μ {x} * ν {y} := prod_prod_le _ _
    _ = 0 := by simp

Depends on / 依赖: prod_prod_le, singleton_prod_singleton
-/
instance prod.instNullSingletonClass_fst [NullSingletonClass μ] :
    NullSingletonClass (Measure.prod μ ν) where
  measure_singleton
| (x, y) => nonpos_iff_eq_zero.mp calc
    μ.prod ν {(x, y)} = μ.prod ν ({x} ×ˢ {y}) := by rw [singleton_prod_singleton]
    _ <= μ {x} * ν {y} := prod_prod_le _ _
    _ = 0 := by simp

/--
Instance `prod.instNullSingletonClass_snd` / 实例 `prod.instNullSingletonClass_snd`

English:
instance prod.instNullSingletonClass_snd
  signature: [NullSingletonClass ν]
  body: by rw [singleton_prod_singleton]
    _ <= μ {x} * ν {y} := prod_prod_le _ _
    _ = 0 := by simp

中文:
实例 乘积.instNullSingletonClass_snd
  签名: [NullSingleton类 ν]
  定义体: by rw [singleton_prod_singleton]
    _ <= μ {x} * ν {y} := prod_prod_le _ _
    _ = 0 := by simp

Depends on / 依赖: prod_prod_le, singleton_prod_singleton
-/
instance prod.instNullSingletonClass_snd [NullSingletonClass ν] :
    NullSingletonClass (Measure.prod μ ν) where
  measure_singleton
| (x, y) => nonpos_iff_eq_zero.mp calc
    μ.prod ν {(x, y)} = μ.prod ν ({x} ×ˢ {y}) := by rw [singleton_prod_singleton]
    _ <= μ {x} * ν {y} := prod_prod_le _ _
    _ = 0 := by simp

variable [SFinite ν]

/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: {s : Set (α × β)} (hs : MeasurableSet s)
  proof: by
  simp_rw [Measure.prod, bind_apply hs (Measurable.map_prodMk_left (ν := ν)).aemeasurable,
    map_apply measurable_prodMk_left hs]

中文:
定理 prod_apply
  条件: {s : 集合 (α × β)} (hs : 可测集 s)
  证明: by
  simp_rw [Measure.prod, bind_apply hs (Measurable.map_prodMk_left (ν := ν)).aemeasurable,
    map_apply measurable_prodMk_left hs]

Depends on / 依赖: Measurable, Measurable.map_prodMk_left, Measure, Measure.prod, aemeasurable, bind_apply, map_apply, map_prodMk_left, measurable_prodMk_left, simp_rw
-/
theorem prod_apply {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  simp_rw [Measure.prod, bind_apply hs (Measurable.map_prodMk_left (ν := ν)).aemeasurable,
    map_apply measurable_prodMk_left hs]

/-- The product measure of the product of two sets is the product of their measures. Note that we
do not need the sets to be measurable. -/
@[simp]
/--
theorem `prod_prod` / 定理 `prod_prod`

English:
theorem prod_prod
  given: (s : Set α) (t : Set β)
  statement: μ.prod ν (s ×ˢ t) = μ s * ν t
  proof: by
  apply (prod_prod_le s t).antisymm
  -- Formalization is based on https://mathoverflow.net/a/254134/136589
  set ST := toMeasurable (μ.prod ν) (s ×ˢ t)
  have hSTm : MeasurableSet ST := measurableSet_toMeasurable _ _
  have hST : s ×ˢ t subseteq ST := subset_toMeasurable _ _
  set f : α -> Real>

中文:
定理 prod_prod
  条件: (s : 集合 α) (t : 集合 β)
  结论: μ.乘积 ν (s ×ˢ t) = μ s * ν t
  证明: by
  apply (prod_prod_le s t).antisymm
  -- Formalization is based on https://mathoverflow.net/a/254134/136589
  set ST := toMeasurable (μ.prod ν) (s ×ˢ t)
  have hSTm : MeasurableSet ST := measurableSet_toMeasurable _ _
  have hST : s ×ˢ t subseteq ST := subset_toMeasurable _ _
  set f : α -> Real>

Depends on / 依赖: antisymm, prod_prod_le
-/
theorem prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  apply (prod_prod_le s t).antisymm
  -- Formalization is based on https://mathoverflow.net/a/254134/136589
  set ST := toMeasurable (μ.prod ν) (s ×ˢ t)
  have hSTm : MeasurableSet ST := measurableSet_toMeasurable _ _
  have hST : s ×ˢ t subseteq ST := subset_toMeasurable _ _
  set f : α -> Real>=0∞ := fun x => ν (Prod.mk x ⁻¹' ST)
  have hfm : Measurable f := measurable_measure_prodMk_left hSTm
  set s' : Set α := { x | ν t <= f x }
have hss' : s subseteq s' := fun x hx => measure_mono fun y hy => hST mk_mem_prod hx hy
  calc
    μ s * ν t <= μ s' * ν t := by gcongr
    _ = ∫⁻ _ in s', ν t ∂μ := by rw [setLIntegral_const, mul_comm]
    _ <= ∫⁻ x in s', f x ∂μ := setLIntegral_mono hfm fun x => id
    _ <= ∫⁻ x, f x ∂μ := lintegral_mono' restrict_le_self le_rfl
    _ = μ.prod ν ST := (prod_apply hSTm).symm
    _ = μ.prod ν (s ×ˢ t) := measure_toMeasurable _

@[simp]
/--
theorem `_root_.MeasureTheory.measureReal_prod_prod` / 定理 `_root_.MeasureTheory.measureReal_prod_prod`

English:
theorem _root_.MeasureTheory.measureReal_prod_prod
  given: (s : Set α) (t : Set β)
  proof: by
  simp only [measureReal_def, prod_prod, ENNReal.toReal_mul]

中文:
定理 _root_.测度论.measure实数_prod_prod
  条件: (s : 集合 α) (t : 集合 β)
  证明: by
  simp only [measureReal_def, prod_prod, ENNReal.toReal_mul]

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, measureReal_def, prod_prod, toReal_mul
-/
theorem _root_.MeasureTheory.measureReal_prod_prod (s : Set α) (t : Set β) :
    (μ.prod ν).real (s ×ˢ t) = μ.real s * ν.real t := by
  simp only [measureReal_def, prod_prod, ENNReal.toReal_mul]

/--
lemma `map_fst_prod` / 引理 `map_fst_prod`

English:
lemma map_fst_prod
  statement: Measure.map Prod.fst (μ.prod ν) = (ν univ) • μ
  proof: by
  ext s hs
  simp [Measure.map_apply measurable_fst hs, ← prod_univ, mul_comm]

中文:
引理 map_fst_prod
  结论: 测度.map 积类型.fst (μ.乘积 ν) = (ν univ) • μ
  证明: by
  ext s hs
  simp [Measure.map_apply measurable_fst hs, ← prod_univ, mul_comm]
-/
@[simp] lemma map_fst_prod : Measure.map Prod.fst (μ.prod ν) = (ν univ) • μ := by
  ext s hs
  simp [Measure.map_apply measurable_fst hs, ← prod_univ, mul_comm]

/--
lemma `_root_.MeasureTheory.measurePreserving_fst` / 引理 `_root_.MeasureTheory.measurePreserving_fst`

English:
lemma _root_.MeasureTheory.measurePreserving_fst
  given: [IsProbabilityMeasure ν]
  proof: ⟨measurable_fst, by rw [map_fst_prod, measure_univ, one_smul]⟩

中文:
引理 _root_.测度论.measurePreserving_fst
  条件: [是概率测度 ν]
  证明: ⟨measurable_fst, by rw [map_fst_prod, measure_univ, one_smul]⟩

Depends on / 依赖: map_fst_prod, measurable_fst, measure_univ, one_smul
-/
lemma _root_.MeasureTheory.measurePreserving_fst [IsProbabilityMeasure ν] :
    MeasurePreserving Prod.fst (μ.prod ν) μ :=
  ⟨measurable_fst, by rw [map_fst_prod, measure_univ, one_smul]⟩

/--
lemma `map_snd_prod` / 引理 `map_snd_prod`

English:
lemma map_snd_prod
  statement: Measure.map Prod.snd (μ.prod ν) = (μ univ) • ν
  proof: by
  ext s hs
  simp [Measure.map_apply measurable_snd hs, ← univ_prod]

中文:
引理 map_snd_prod
  结论: 测度.map 积类型.snd (μ.乘积 ν) = (μ univ) • ν
  证明: by
  ext s hs
  simp [Measure.map_apply measurable_snd hs, ← univ_prod]
-/
@[simp] lemma map_snd_prod : Measure.map Prod.snd (μ.prod ν) = (μ univ) • ν := by
  ext s hs
  simp [Measure.map_apply measurable_snd hs, ← univ_prod]

/--
lemma `_root_.MeasureTheory.measurePreserving_snd` / 引理 `_root_.MeasureTheory.measurePreserving_snd`

English:
lemma _root_.MeasureTheory.measurePreserving_snd
  given: [IsProbabilityMeasure μ]
  proof: ⟨measurable_snd, by rw [map_snd_prod, measure_univ, one_smul]⟩

中文:
引理 _root_.测度论.measurePreserving_snd
  条件: [是概率测度 μ]
  证明: ⟨measurable_snd, by rw [map_snd_prod, measure_univ, one_smul]⟩

Depends on / 依赖: map_snd_prod, measurable_snd, measure_univ, one_smul
-/
lemma _root_.MeasureTheory.measurePreserving_snd [IsProbabilityMeasure μ] :
    MeasurePreserving Prod.snd (μ.prod ν) ν :=
  ⟨measurable_snd, by rw [map_snd_prod, measure_univ, one_smul]⟩

/--
Instance `prod.instIsOpenPosMeasure` / 实例 `prod.instIsOpenPosMeasure`

English:
instance prod.instIsOpenPosMeasure
  signature: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  body: by
  constructor
  rintro U U_open ⟨⟨x, y⟩, hxy⟩
  rcases isOpen_prod_iff.1 U_open x y hxy with ⟨u, v, u_open, v_open, xu, yv, huv⟩
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono huv))
  simp only [prod_prod, CanonicallyOrderedAdd.mul_pos]
  constructor
  · exact u_open.measure_pos μ ⟨x, xu⟩
  ·

中文:
实例 乘积.instIsOpenPosMeasure
  签名: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y]
  定义体: by
  constructor
  rintro U U_open ⟨⟨x, y⟩, hxy⟩
  rcases isOpen_prod_iff.1 U_open x y hxy with ⟨u, v, u_open, v_open, xu, yv, huv⟩
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono huv))
  simp only [prod_prod, CanonicallyOrderedAdd.mul_pos]
  constructor
  · exact u_open.measure_pos μ ⟨x, xu⟩
  ·

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.mul_pos, U_open, isOpen_prod_iff, lt_of_lt_of_le, measure_mono, measure_pos, mul_pos, ne_of_gt, prod_prod, u_open, u_open.measure_pos, v_open, v_open.measure_pos
-/
instance prod.instIsOpenPosMeasure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {m : MeasurableSpace X} {μ : Measure X} [IsOpenPosMeasure μ] {m' : MeasurableSpace Y}
    {ν : Measure Y} [IsOpenPosMeasure ν] [SFinite ν] : IsOpenPosMeasure (μ.prod ν) := by
  constructor
  rintro U U_open ⟨⟨x, y⟩, hxy⟩
  rcases isOpen_prod_iff.1 U_open x y hxy with ⟨u, v, u_open, v_open, xu, yv, huv⟩
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono huv))
  simp only [prod_prod, CanonicallyOrderedAdd.mul_pos]
  constructor
  · exact u_open.measure_pos μ ⟨x, xu⟩
  · exact v_open.measure_pos ν ⟨y, yv⟩

instance {X Y : Type*}
    [TopologicalSpace X] [MeasureSpace X] [IsOpenPosMeasure (volume : Measure X)]
    [TopologicalSpace Y] [MeasureSpace Y] [IsOpenPosMeasure (volume : Measure Y)]
    [SFinite (volume : Measure Y)] : IsOpenPosMeasure (volume : Measure (X × Y)) :=
  prod.instIsOpenPosMeasure

/--
theorem `FiniteAtFilter.prod` / 定理 `FiniteAtFilter.prod`

English:
theorem FiniteAtFilter.prod
  statement: {X Y : Type*} {m : MeasurableSpace X} {μ : Measure X}
  proof: by
  rcases hμ with ⟨s, hs, hμs⟩
  rcases hν with ⟨t, ht, hνt⟩
  use s ×ˢ t, Filter.prod_mem_prod hs ht
  grw [prod_prod_le]
  exact ENNReal.mul_lt_top hμs hνt

中文:
定理 FiniteAtFilter.乘积
  结论: {X Y : 类型} {m : 可测空间 X} {μ : 测度 X}
  证明: by
  rcases hμ with ⟨s, hs, hμs⟩
  rcases hν with ⟨t, ht, hνt⟩
  use s ×ˢ t, Filter.prod_mem_prod hs ht
  grw [prod_prod_le]
  exact ENNReal.mul_lt_top hμs hνt
-/
protected theorem FiniteAtFilter.prod {X Y : Type*} {m : MeasurableSpace X} {μ : Measure X}
    {m' : MeasurableSpace Y} {ν : Measure Y} {l : Filter X} {l' : Filter Y}
    (hμ : μ.FiniteAtFilter l) (hν : ν.FiniteAtFilter l') :
    (μ.prod ν).FiniteAtFilter (l ×ˢ l') := by
  rcases hμ with ⟨s, hs, hμs⟩
  rcases hν with ⟨t, ht, hνt⟩
  use s ×ˢ t, Filter.prod_mem_prod hs ht
  grw [prod_prod_le]
  exact ENNReal.mul_lt_top hμs hνt

/--
Instance `prod.instIsLocallyFiniteMeasure` / 实例 `prod.instIsLocallyFiniteMeasure`

English:
instance prod.instIsLocallyFiniteMeasure
  signature: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  body: by
    rw [nhds_prod_eq]
.prod ν.finiteAt_nhds _ exact μ.finiteAt_nhds _

中文:
实例 乘积.instIsLocallyFiniteMeasure
  签名: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y]
  定义体: by
    rw [nhds_prod_eq]
.prod ν.finiteAt_nhds _ exact μ.finiteAt_nhds _

Depends on / 依赖: finiteAt_nhds, nhds_prod_eq
-/
instance prod.instIsLocallyFiniteMeasure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {m : MeasurableSpace X} {μ : Measure X} [IsLocallyFiniteMeasure μ] {m' : MeasurableSpace Y}
    {ν : Measure Y} [IsLocallyFiniteMeasure ν] : IsLocallyFiniteMeasure (μ.prod ν) where
  finiteAtNhds x := by
    rw [nhds_prod_eq]
.prod ν.finiteAt_nhds _ exact μ.finiteAt_nhds _

instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {m : MeasureSpace X} [IsLocallyFiniteMeasure (volume : Measure X)]
    {m' : MeasureSpace Y} [IsLocallyFiniteMeasure (volume : Measure Y)] :
    IsLocallyFiniteMeasure (volume : Measure (X × Y)) :=
  prod.instIsLocallyFiniteMeasure

/--
Instance `prod.instIsFiniteMeasure` / 实例 `prod.instIsFiniteMeasure`

English:
instance prod.instIsFiniteMeasure
  signature: {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  body: by
  constructor
  rw [← univ_prod_univ]; rw [prod_prod]
  finiteness

中文:
实例 乘积.instIsFiniteMeasure
  签名: {α β : 类型} {mα : 可测空间 α} {mβ : 可测空间 β}
  定义体: by
  constructor
  rw [← univ_prod_univ]; rw [prod_prod]
  finiteness

Depends on / 依赖: finiteness, prod_prod, univ_prod_univ
-/
instance prod.instIsFiniteMeasure {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ.prod ν) := by
  constructor
  rw [← univ_prod_univ]; rw [prod_prod]
  finiteness

instance {α β : Type*} [MeasureSpace α] [MeasureSpace β] [IsFiniteMeasure (volume : Measure α)]
    [IsFiniteMeasure (volume : Measure β)] : IsFiniteMeasure (volume : Measure (α × β)) :=
  prod.instIsFiniteMeasure _ _

/--
Instance `prod.instIsProbabilityMeasure` / 实例 `prod.instIsProbabilityMeasure`

English:
instance prod.instIsProbabilityMeasure
  signature: {α β : Type*} {mα : MeasurableSpace α}
  body: ⟨by rw [← univ_prod_univ, prod_prod, measure_univ, measure_univ, mul_one]⟩

中文:
实例 乘积.instIsProbabilityMeasure
  签名: {α β : 类型} {mα : 可测空间 α}
  定义体: ⟨by rw [← univ_prod_univ, prod_prod, measure_univ, measure_univ, mul_one]⟩

Depends on / 依赖: measure_univ, mul_one, prod_prod, univ_prod_univ
-/
instance prod.instIsProbabilityMeasure {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (μ.prod ν) :=
  ⟨by rw [← univ_prod_univ, prod_prod, measure_univ, measure_univ, mul_one]⟩

instance {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [IsProbabilityMeasure (volume : Measure α)] [IsProbabilityMeasure (volume : Measure β)] :
    IsProbabilityMeasure (volume : Measure (α × β)) :=
  prod.instIsProbabilityMeasure _ _

/--
Instance `prod.instIsFiniteMeasureOnCompacts` / 实例 `prod.instIsFiniteMeasureOnCompacts`

English:
instance prod.instIsFiniteMeasureOnCompacts
  signature: {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
  body: calc
    μ.prod ν K <= μ.prod ν ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) := measure_mono subset_prod
    _ <= μ (Prod.fst '' K) * ν (Prod.snd '' K) := prod_prod_le _ _
    _ < ∞ :=
      mul_lt_top (hK.image continuous_fst).measure_lt_top (hK.image continuous_snd).measure_lt_top

中文:
实例 乘积.instIsFiniteMeasureOnCompacts
  签名: {α β : 类型} [拓扑空间 α] [拓扑空间 β]
  定义体: calc
    μ.prod ν K <= μ.prod ν ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) := measure_mono subset_prod
    _ <= μ (Prod.fst '' K) * ν (Prod.snd '' K) := prod_prod_le _ _
    _ < ∞ :=
      mul_lt_top (hK.image continuous_fst).measure_lt_top (hK.image continuous_snd).measure_lt_top
-/
instance prod.instIsFiniteMeasureOnCompacts {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (μ.prod ν) where
  lt_top_of_isCompact K hK := calc
    μ.prod ν K <= μ.prod ν ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) := measure_mono subset_prod
    _ <= μ (Prod.fst '' K) * ν (Prod.snd '' K) := prod_prod_le _ _
    _ < ∞ :=
      mul_lt_top (hK.image continuous_fst).measure_lt_top (hK.image continuous_snd).measure_lt_top

instance {X Y : Type*}
    [TopologicalSpace X] [MeasureSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [TopologicalSpace Y] [MeasureSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)] :
    IsFiniteMeasureOnCompacts (volume : Measure (X × Y)) :=
  prod.instIsFiniteMeasureOnCompacts _ _


open IsUnifLocDoublingMeasure in
/--
Instance `_root_.IsUnifLocDoublingMeasure.prod` / 实例 `_root_.IsUnifLocDoublingMeasure.prod`

English:
instance _root_.IsUnifLocDoublingMeasure.prod
  signature: {X Y : Type*}
  body: by
  constructor
  use doublingConstant μ * doublingConstant ν
  filter_upwards [eventually_measure_le_doublingConstant_mul μ,
    eventually_measure_le_doublingConstant_mul ν] with r hμr hνr x
  rw [← closedBall_prod_same]; rw [prod_prod]; rw [← closedBall_prod_same]; rw [prod_prod]
  grw [hμr, hνr

中文:
实例 _root_.是UnifLocDoublingMeasure.乘积
  签名: {X Y : 类型}
  定义体: by
  constructor
  use doublingConstant μ * doublingConstant ν
  filter_upwards [eventually_measure_le_doublingConstant_mul μ,
    eventually_measure_le_doublingConstant_mul ν] with r hμr hνr x
  rw [← closedBall_prod_same]; rw [prod_prod]; rw [← closedBall_prod_same]; rw [prod_prod]
  grw [hμr, hνr

Depends on / 依赖: ENNReal, ENNReal.coe_mul, closedBall_prod_same, coe_mul, doublingConstant, eventually_measure_le_doublingConstant_mul, filter_upwards, mul_mul_mul_comm, prod_prod
-/
instance _root_.IsUnifLocDoublingMeasure.prod {X Y : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [PseudoMetricSpace Y] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    [IsUnifLocDoublingMeasure μ] [IsUnifLocDoublingMeasure ν] :
    IsUnifLocDoublingMeasure (μ.prod ν) := by
  constructor
  use doublingConstant μ * doublingConstant ν
  filter_upwards [eventually_measure_le_doublingConstant_mul μ,
    eventually_measure_le_doublingConstant_mul ν] with r hμr hνr x
  rw [← closedBall_prod_same]; rw [prod_prod]; rw [← closedBall_prod_same]; rw [prod_prod]
  grw [hμr, hνr, ENNReal.coe_mul, mul_mul_mul_comm]

/--
Instance `IsUnifLocDoublingMeasure.volume_prod` / 实例 `IsUnifLocDoublingMeasure.volume_prod`

English:
instance IsUnifLocDoublingMeasure.volume_prod
  signature: {X Y : Type*} [PseudoMetricSpace X] [MeasureSpace X]
  body: .prod _ _

中文:
实例 是UnifLocDoublingMeasure.volume_prod
  签名: {X Y : 类型} [伪度量空间 X] [测度空间 X]
  定义体: .prod _ _
-/
instance IsUnifLocDoublingMeasure.volume_prod {X Y : Type*} [PseudoMetricSpace X] [MeasureSpace X]
    [PseudoMetricSpace Y] [MeasureSpace Y] [SFinite (volume : Measure Y)]
    [IsUnifLocDoublingMeasure (volume : Measure X)]
    [IsUnifLocDoublingMeasure (volume : Measure Y)] :
    IsUnifLocDoublingMeasure (volume : Measure (X × Y)) :=
  .prod _ _

/--
theorem `ae_measure_lt_top` / 定理 `ae_measure_lt_top`

English:
theorem ae_measure_lt_top
  given: {s : Set (α × β)} (hs : MeasurableSet s) (h2s : (μ.prod ν) s != ∞)
  proof: by
  rw [prod_apply hs] at h2s
  exact ae_lt_top (measurable_measure_prodMk_left hs) h2s

omit [SFinite ν] in

中文:
定理 ae_measure_lt_top
  条件: {s : 集合 (α × β)} (hs : 可测集 s) (h2s : (μ.乘积 ν) s != ∞)
  证明: by
  rw [prod_apply hs] at h2s
  exact ae_lt_top (measurable_measure_prodMk_left hs) h2s

omit [SFinite ν] in

Depends on / 依赖: ae_lt_top, measurable_measure_prodMk_left, prod_apply
-/
theorem ae_measure_lt_top {s : Set (α × β)} (hs : MeasurableSet s) (h2s : (μ.prod ν) s != ∞) :
    forallᵐ x ∂μ, ν (Prod.mk x ⁻¹' s) < ∞ := by
  rw [prod_apply hs] at h2s
  exact ae_lt_top (measurable_measure_prodMk_left hs) h2s

omit [SFinite ν] in
/--
theorem `measure_prod_null_of_ae_null` / 定理 `measure_prod_null_of_ae_null`

English:
theorem measure_prod_null_of_ae_null
  statement: {s : Set (α × β)} (hsm : MeasurableSet s)
  proof: by
  rw [← nonpos_iff_eq_zero]
  calc
    μ.prod ν s <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := prod_apply_le hsm
    _ = 0 := by simp [lintegral_congr_ae hs]

中文:
定理 measure_prod_null_of_ae_null
  结论: {s : 集合 (α × β)} (hsm : 可测集 s)
  证明: by
  rw [← nonpos_iff_eq_zero]
  calc
    μ.prod ν s <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := prod_apply_le hsm
    _ = 0 := by simp [lintegral_congr_ae hs]

Depends on / 依赖: Prod.mk, lintegral_congr_ae, nonpos_iff_eq_zero, prod_apply_le
-/
theorem measure_prod_null_of_ae_null {s : Set (α × β)} (hsm : MeasurableSet s)
    (hs : (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0) : μ.prod ν s = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc
    μ.prod ν s <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := prod_apply_le hsm
    _ = 0 := by simp [lintegral_congr_ae hs]

/--
theorem `measure_prod_null` / 定理 `measure_prod_null`

English:
theorem measure_prod_null
  given: {s : Set (α × β)} (hs : MeasurableSet s)
  proof: by
  rw [prod_apply hs]; rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hs)]

中文:
定理 measure_prod_null
  条件: {s : 集合 (α × β)} (hs : 可测集 s)
  证明: by
  rw [prod_apply hs]; rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hs)]

Depends on / 依赖: lintegral_eq_zero_iff, measurable_measure_prodMk_left, prod_apply
-/
theorem measure_prod_null {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  rw [prod_apply hs]; rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hs)]

/--
theorem `measure_ae_null_of_prod_null` / 定理 `measure_ae_null_of_prod_null`

English:
theorem measure_ae_null_of_prod_null
  given: {s : Set (α × β)} (h : μ.prod ν s = 0)
  proof: by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  rw [measure_prod_null mt] at ht
  rw [eventuallyLE_antisymm_iff]
  exact
    ⟨EventuallyLE.trans_eq (Eventually.of_forall fun x => measure_mono (preimage_mono hst)) ht,
      Eventually.of_forall fun x => zero_le⟩

omit [SFinite 

中文:
定理 measure_ae_null_of_prod_null
  条件: {s : 集合 (α × β)} (h : μ.乘积 ν s = 0)
  证明: by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  rw [measure_prod_null mt] at ht
  rw [eventuallyLE_antisymm_iff]
  exact
    ⟨EventuallyLE.trans_eq (Eventually.of_forall fun x => measure_mono (preimage_mono hst)) ht,
      Eventually.of_forall fun x => zero_le⟩

omit [SFinite 

Depends on / 依赖: Eventually, Eventually.of_forall, EventuallyLE, EventuallyLE.trans_eq, eventuallyLE_antisymm_iff, exists_measurable_superset_of_null, measure_mono, measure_prod_null, of_forall, preimage_mono, trans_eq, zero_le
-/
theorem measure_ae_null_of_prod_null {s : Set (α × β)} (h : μ.prod ν s = 0) :
    (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  rw [measure_prod_null mt] at ht
  rw [eventuallyLE_antisymm_iff]
  exact
    ⟨EventuallyLE.trans_eq (Eventually.of_forall fun x => measure_mono (preimage_mono hst)) ht,
      Eventually.of_forall fun x => zero_le⟩

omit [SFinite ν] in
/--
theorem `AbsolutelyContinuous.prod` / 定理 `AbsolutelyContinuous.prod`

English:
theorem AbsolutelyContinuous.prod
  given: [SFinite ν'] (h1 : μ ≪ μ') (h2 : ν ≪ ν')
  proof: by
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  apply measure_prod_null_of_ae_null hs
  rw [measure_prod_null hs] at h2s
  exact (h2s.filter_mono h1.ae_le).mono fun _ h => h2 h

omit [SFinite ν] in

中文:
定理 AbsolutelyContinuous.乘积
  条件: [SFinite ν'] (h1 : μ ≪ μ') (h2 : ν ≪ ν')
  证明: by
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  apply measure_prod_null_of_ae_null hs
  rw [measure_prod_null hs] at h2s
  exact (h2s.filter_mono h1.ae_le).mono fun _ h => h2 h

omit [SFinite ν] in

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, ae_le, filter_mono, h1.ae_le, h2s.filter_mono, measure_prod_null, measure_prod_null_of_ae_null
-/
theorem AbsolutelyContinuous.prod [SFinite ν'] (h1 : μ ≪ μ') (h2 : ν ≪ ν') :
    μ.prod ν ≪ μ'.prod ν' := by
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  apply measure_prod_null_of_ae_null hs
  rw [measure_prod_null hs] at h2s
  exact (h2s.filter_mono h1.ae_le).mono fun _ h => h2 h

omit [SFinite ν] in
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: [SFinite ν'] (h1 : μ <= μ') (h2 : ν <= ν')
  statement: μ.prod ν <= μ'.prod ν'
  proof: by
  apply Measure.le_iff.2 (fun s hs => ?_)
  calc μ.prod ν s
  _ <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := prod_apply_le hs
  _ <= ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ' := by gcongr
  _ = (μ'.prod ν') s := (prod_apply hs).symm

中文:
定理 prod_mono
  条件: [SFinite ν'] (h1 : μ <= μ') (h2 : ν <= ν')
  结论: μ.乘积 ν <= μ'.乘积 ν'
  证明: by
  apply Measure.le_iff.2 (fun s hs => ?_)
  calc μ.prod ν s
  _ <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := prod_apply_le hs
  _ <= ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ' := by gcongr
  _ = (μ'.prod ν') s := (prod_apply hs).symm
-/
@[gcongr] theorem prod_mono [SFinite ν'] (h1 : μ <= μ') (h2 : ν <= ν') : μ.prod ν <= μ'.prod ν' := by
  apply Measure.le_iff.2 (fun s hs => ?_)
  calc μ.prod ν s
  _ <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := prod_apply_le hs
  _ <= ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ' := by gcongr
  _ = (μ'.prod ν') s := (prod_apply hs).symm

/--
theorem `ae_ae_of_ae_prod` / 定理 `ae_ae_of_ae_prod`

English:
theorem ae_ae_of_ae_prod
  given: {p : α × β -> Prop} (h : forallᵐ z ∂μ.prod ν, p z)
  proof: measure_ae_null_of_prod_null h

中文:
定理 ae_ae_of_ae_prod
  条件: {p : α × β -> 命题} (h : 对任意ᵐ z ∂μ.乘积 ν, p z)
  证明: measure_ae_null_of_prod_null h

Depends on / 依赖: measure_ae_null_of_prod_null
-/
theorem ae_ae_of_ae_prod {p : α × β -> Prop} (h : forallᵐ z ∂μ.prod ν, p z) :
    forallᵐ x ∂μ, forallᵐ y ∂ν, p (x, y) :=
  measure_ae_null_of_prod_null h

/--
theorem `ae_ae_eq_curry_of_prod` / 定理 `ae_ae_eq_curry_of_prod`

English:
theorem ae_ae_eq_curry_of_prod
  given: {γ : Type*} {f g : α × β -> γ} (h : f =ᵐ[μ.prod ν] g)
  proof: ae_ae_of_ae_prod h

中文:
定理 ae_ae_eq_curry_of_prod
  条件: {γ : 类型} {f g : α × β -> γ} (h : f =ᵐ[μ.乘积 ν] g)
  证明: ae_ae_of_ae_prod h

Depends on / 依赖: ae_ae_of_ae_prod
-/
theorem ae_ae_eq_curry_of_prod {γ : Type*} {f g : α × β -> γ} (h : f =ᵐ[μ.prod ν] g) :
    forallᵐ x ∂μ, curry f x =ᵐ[ν] curry g x :=
  ae_ae_of_ae_prod h

/--
theorem `ae_ae_eq_of_ae_eq_uncurry` / 定理 `ae_ae_eq_of_ae_eq_uncurry`

English:
theorem ae_ae_eq_of_ae_eq_uncurry
  statement: {γ : Type*} {f g : α -> β -> γ}
  proof: ae_ae_eq_curry_of_prod h

中文:
定理 ae_ae_eq_of_ae_eq_uncurry
  结论: {γ : 类型} {f g : α -> β -> γ}
  证明: ae_ae_eq_curry_of_prod h

Depends on / 依赖: ae_ae_eq_curry_of_prod
-/
theorem ae_ae_eq_of_ae_eq_uncurry {γ : Type*} {f g : α -> β -> γ}
    (h : uncurry f =ᵐ[μ.prod ν] uncurry g) : forallᵐ x ∂μ, f x =ᵐ[ν] g x :=
  ae_ae_eq_curry_of_prod h

/--
theorem `ae_prod_iff_ae_ae` / 定理 `ae_prod_iff_ae_ae`

English:
theorem ae_prod_iff_ae_ae
  given: {p : α × β -> Prop} (hp : MeasurableSet {x | p x})
  proof: measure_prod_null hp.compl

中文:
定理 ae_prod_iff_ae_ae
  条件: {p : α × β -> 命题} (hp : 可测集 {x | p x})
  证明: measure_prod_null hp.compl

Depends on / 依赖: hp.compl, measure_prod_null
-/
theorem ae_prod_iff_ae_ae {p : α × β -> Prop} (hp : MeasurableSet {x | p x}) :
    (forallᵐ z ∂μ.prod ν, p z) ↔ forallᵐ x ∂μ, forallᵐ y ∂ν, p (x, y) :=
  measure_prod_null hp.compl

/--
theorem `ae_prod_mem_iff_ae_ae_mem` / 定理 `ae_prod_mem_iff_ae_ae_mem`

English:
theorem ae_prod_mem_iff_ae_ae_mem
  given: {s : Set (α × β)} (hs : MeasurableSet s)
  proof: measure_prod_null hs.compl

omit [SFinite ν] in
@[fun_prop]

中文:
定理 ae_prod_mem_iff_ae_ae_mem
  条件: {s : 集合 (α × β)} (hs : 可测集 s)
  证明: measure_prod_null hs.compl

omit [SFinite ν] in
@[fun_prop]

Depends on / 依赖: hs.compl, measure_prod_null
-/
theorem ae_prod_mem_iff_ae_ae_mem {s : Set (α × β)} (hs : MeasurableSet s) :
    (forallᵐ z ∂μ.prod ν, z in s) ↔ forallᵐ x ∂μ, forallᵐ y ∂ν, (x, y) in s :=
  measure_prod_null hs.compl

omit [SFinite ν] in
@[fun_prop]
/--
theorem `quasiMeasurePreserving_fst` / 定理 `quasiMeasurePreserving_fst`

English:
theorem quasiMeasurePreserving_fst
  statement: QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
  proof: by
  refine ⟨measurable_fst, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_fst hs]; rw [← prod_univ]; rw [← nonpos_iff_eq_zero]
  refine (prod_prod_le _ _).trans_eq ?_
  rw [h2s]; rw [zero_mul]

omit [SFinite ν] in
@[fun_prop]

中文:
定理 quasiMeasurePreserving_fst
  结论: 拟保测 积类型.fst (μ.乘积 ν) μ
  证明: by
  refine ⟨measurable_fst, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_fst hs]; rw [← prod_univ]; rw [← nonpos_iff_eq_zero]
  refine (prod_prod_le _ _).trans_eq ?_
  rw [h2s]; rw [zero_mul]

omit [SFinite ν] in
@[fun_prop]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, map_apply, measurable_fst, nonpos_iff_eq_zero, prod_prod_le, prod_univ, trans_eq, zero_mul
-/
theorem quasiMeasurePreserving_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ := by
  refine ⟨measurable_fst, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_fst hs]; rw [← prod_univ]; rw [← nonpos_iff_eq_zero]
  refine (prod_prod_le _ _).trans_eq ?_
  rw [h2s]; rw [zero_mul]

omit [SFinite ν] in
@[fun_prop]
/--
theorem `quasiMeasurePreserving_snd` / 定理 `quasiMeasurePreserving_snd`

English:
theorem quasiMeasurePreserving_snd
  statement: QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
  proof: by
  refine ⟨measurable_snd, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_snd hs]; rw [← univ_prod]; rw [← nonpos_iff_eq_zero]
  refine (prod_prod_le _ _).trans_eq ?_
  rw [h2s]; rw [mul_zero]

omit [SFinite ν] in

中文:
定理 quasiMeasurePreserving_snd
  结论: 拟保测 积类型.snd (μ.乘积 ν) ν
  证明: by
  refine ⟨measurable_snd, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_snd hs]; rw [← univ_prod]; rw [← nonpos_iff_eq_zero]
  refine (prod_prod_le _ _).trans_eq ?_
  rw [h2s]; rw [mul_zero]

omit [SFinite ν] in

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, map_apply, measurable_snd, mul_zero, nonpos_iff_eq_zero, prod_prod_le, trans_eq, univ_prod
-/
theorem quasiMeasurePreserving_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν := by
  refine ⟨measurable_snd, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_snd hs]; rw [← univ_prod]; rw [← nonpos_iff_eq_zero]
  refine (prod_prod_le _ _).trans_eq ?_
  rw [h2s]; rw [mul_zero]

omit [SFinite ν] in
/--
lemma `set_prod_ae_eq` / 引理 `set_prod_ae_eq`

English:
lemma set_prod_ae_eq
  given: {s s' : Set α} {t t' : Set β} (hs : s =ᵐ[μ] s') (ht : t =ᵐ[ν] t')
  proof: (quasiMeasurePreserving_fst.preimage_ae_eq hs).inter
    (quasiMeasurePreserving_snd.preimage_ae_eq ht)

中文:
引理 set_prod_ae_eq
  条件: {s s' : 集合 α} {t t' : 集合 β} (hs : s =ᵐ[μ] s') (ht : t =ᵐ[ν] t')
  证明: (quasiMeasurePreserving_fst.preimage_ae_eq hs).inter
    (quasiMeasurePreserving_snd.preimage_ae_eq ht)

Depends on / 依赖: preimage_ae_eq, quasiMeasurePreserving_fst, quasiMeasurePreserving_fst.preimage_ae_eq, quasiMeasurePreserving_snd, quasiMeasurePreserving_snd.preimage_ae_eq
-/
lemma set_prod_ae_eq {s s' : Set α} {t t' : Set β} (hs : s =ᵐ[μ] s') (ht : t =ᵐ[ν] t') :
    (s ×ˢ t : Set (α × β)) =ᵐ[μ.prod ν] (s' ×ˢ t' : Set (α × β)) :=
  (quasiMeasurePreserving_fst.preimage_ae_eq hs).inter
    (quasiMeasurePreserving_snd.preimage_ae_eq ht)

/--
lemma `measure_prod_compl_eq_zero` / 引理 `measure_prod_compl_eq_zero`

English:
lemma measure_prod_compl_eq_zero
  statement: {s : Set α} {t : Set β}
  proof: by
  rw [Set.compl_prod_eq_union]; rw [measure_union_null_iff]
  simp [s_ae_univ, t_ae_univ]

omit [SFinite ν] in

中文:
引理 measure_prod_compl_eq_zero
  结论: {s : 集合 α} {t : 集合 β}
  证明: by
  rw [Set.compl_prod_eq_union]; rw [measure_union_null_iff]
  simp [s_ae_univ, t_ae_univ]

omit [SFinite ν] in

Depends on / 依赖: Set.compl_prod_eq_union, compl_prod_eq_union, measure_union_null_iff, s_ae_univ, t_ae_univ
-/
lemma measure_prod_compl_eq_zero {s : Set α} {t : Set β}
    (s_ae_univ : μ sᶜ = 0) (t_ae_univ : ν tᶜ = 0) :
    μ.prod ν (s ×ˢ t)ᶜ = 0 := by
  rw [Set.compl_prod_eq_union]; rw [measure_union_null_iff]
  simp [s_ae_univ, t_ae_univ]

omit [SFinite ν] in
/--
lemma `_root_.MeasureTheory.NullMeasurableSet.prod` / 引理 `_root_.MeasureTheory.NullMeasurableSet.prod`

English:
lemma _root_.MeasureTheory.NullMeasurableSet.prod
  statement: {s : Set α} {t : Set β}
  proof: let ⟨s₀, mble_s₀, s_aeeq_s₀⟩ := s_mble
  let ⟨t₀, mble_t₀, t_aeeq_t₀⟩ := t_mble
  ⟨s₀ ×ˢ t₀, ⟨mble_s₀.prod mble_t₀, set_prod_ae_eq s_aeeq_s₀ t_aeeq_t₀⟩⟩

中文:
引理 _root_.测度论.NullMeasurableSet.乘积
  结论: {s : 集合 α} {t : 集合 β}
  证明: let ⟨s₀, mble_s₀, s_aeeq_s₀⟩ := s_mble
  let ⟨t₀, mble_t₀, t_aeeq_t₀⟩ := t_mble
  ⟨s₀ ×ˢ t₀, ⟨mble_s₀.prod mble_t₀, set_prod_ae_eq s_aeeq_s₀ t_aeeq_t₀⟩⟩

Depends on / 依赖: s_mble, set_prod_ae_eq, t_mble
-/
lemma _root_.MeasureTheory.NullMeasurableSet.prod {s : Set α} {t : Set β}
    (s_mble : NullMeasurableSet s μ) (t_mble : NullMeasurableSet t ν) :
    NullMeasurableSet (s ×ˢ t) (μ.prod ν) :=
  let ⟨s₀, mble_s₀, s_aeeq_s₀⟩ := s_mble
  let ⟨t₀, mble_t₀, t_aeeq_t₀⟩ := t_mble
  ⟨s₀ ×ˢ t₀, ⟨mble_s₀.prod mble_t₀, set_prod_ae_eq s_aeeq_s₀ t_aeeq_t₀⟩⟩

/--
lemma `_root_.MeasureTheory.NullMeasurableSet.right_of_prod` / 引理 `_root_.MeasureTheory.NullMeasurableSet.right_of_prod`

English:
lemma _root_.MeasureTheory.NullMeasurableSet.right_of_prod
  statement: {s : Set α} {t : Set β}
  proof: by
  rcases h with ⟨u, hum, hu⟩
  obtain ⟨x, hxs, hx⟩ : exists x in s, (Prod.mk x ⁻¹' (s ×ˢ t)) =ᵐ[ν] (Prod.mk x ⁻¹' u) :=
    ((frequently_ae_iff.2 hs).and_eventually (ae_ae_eq_curry_of_prod hu)).exists
  refine ⟨Prod.mk x ⁻¹' u, measurable_prodMk_left hum, ?_⟩
  rwa [mk_preimage_prod_right hxs] at

中文:
引理 _root_.测度论.NullMeasurableSet.right_of_prod
  结论: {s : 集合 α} {t : 集合 β}
  证明: by
  rcases h with ⟨u, hum, hu⟩
  obtain ⟨x, hxs, hx⟩ : exists x in s, (Prod.mk x ⁻¹' (s ×ˢ t)) =ᵐ[ν] (Prod.mk x ⁻¹' u) :=
    ((frequently_ae_iff.2 hs).and_eventually (ae_ae_eq_curry_of_prod hu)).exists
  refine ⟨Prod.mk x ⁻¹' u, measurable_prodMk_left hum, ?_⟩
  rwa [mk_preimage_prod_right hxs] at

Depends on / 依赖: Prod.mk, ae_ae_eq_curry_of_prod, and_eventually, frequently_ae_iff, measurable_prodMk_left, mk_preimage_prod_right
-/
lemma _root_.MeasureTheory.NullMeasurableSet.right_of_prod {s : Set α} {t : Set β}
    (h : NullMeasurableSet (s ×ˢ t) (μ.prod ν)) (hs : μ s != 0) : NullMeasurableSet t ν := by
  rcases h with ⟨u, hum, hu⟩
  obtain ⟨x, hxs, hx⟩ : exists x in s, (Prod.mk x ⁻¹' (s ×ˢ t)) =ᵐ[ν] (Prod.mk x ⁻¹' u) :=
    ((frequently_ae_iff.2 hs).and_eventually (ae_ae_eq_curry_of_prod hu)).exists
  refine ⟨Prod.mk x ⁻¹' u, measurable_prodMk_left hum, ?_⟩
  rwa [mk_preimage_prod_right hxs] at hx

/--
lemma `_root_.MeasureTheory.NullMeasurableSet.of_preimage_snd` / 引理 `_root_.MeasureTheory.NullMeasurableSet.of_preimage_snd`

English:
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_snd
  statement: [NeZero μ] {t : Set β}
  proof: .right_of_prod (by rwa [univ_prod]) (NeZero.ne (μ univ))

中文:
引理 _root_.测度论.NullMeasurableSet.of_preimage_snd
  结论: [NeZero μ] {t : 集合 β}
  证明: .right_of_prod (by rwa [univ_prod]) (NeZero.ne (μ univ))

Depends on / 依赖: NeZero, NeZero.ne, right_of_prod, univ_prod
-/
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_snd [NeZero μ] {t : Set β}
    (h : NullMeasurableSet (Prod.snd ⁻¹' t) (μ.prod ν)) : NullMeasurableSet t ν :=
  .right_of_prod (by rwa [univ_prod]) (NeZero.ne (μ univ))

/--
lemma `nullMeasurableSet_preimage_snd` / 引理 `nullMeasurableSet_preimage_snd`

English:
lemma nullMeasurableSet_preimage_snd
  given: [NeZero μ] {t : Set β}
  proof: ⟨.of_preimage_snd, (.preimage · quasiMeasurePreserving_snd)⟩

中文:
引理 nullMeasurableSet_preimage_snd
  条件: [NeZero μ] {t : 集合 β}
  证明: ⟨.of_preimage_snd, (.preimage · quasiMeasurePreserving_snd)⟩

Depends on / 依赖: of_preimage_snd, preimage, quasiMeasurePreserving_snd
-/
lemma nullMeasurableSet_preimage_snd [NeZero μ] {t : Set β} :
    NullMeasurableSet (Prod.snd ⁻¹' t) (μ.prod ν) ↔ NullMeasurableSet t ν :=
  ⟨.of_preimage_snd, (.preimage · quasiMeasurePreserving_snd)⟩

/--
lemma `nullMeasurable_comp_snd` / 引理 `nullMeasurable_comp_snd`

English:
lemma nullMeasurable_comp_snd
  given: [NeZero μ] {f : β -> γ}
  proof: forall₂_congr fun s _ => nullMeasurableSet_preimage_snd (t := f ⁻¹' s)

中文:
引理 nullMeasurable_comp_snd
  条件: [NeZero μ] {f : β -> γ}
  证明: forall₂_congr fun s _ => nullMeasurableSet_preimage_snd (t := f ⁻¹' s)

Depends on / 依赖: nullMeasurableSet_preimage_snd
-/
lemma nullMeasurable_comp_snd [NeZero μ] {f : β -> γ} :
    NullMeasurable (f ∘ Prod.snd) (μ.prod ν) ↔ NullMeasurable f ν :=
  forall₂_congr fun s _ => nullMeasurableSet_preimage_snd (t := f ⁻¹' s)

/--
Definition of `FiniteSpanningSetsIn.prod` / `FiniteSpanningSetsIn.prod` 的定义

English:
definition FiniteSpanningSetsIn.prod
  signature: {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
  body: by
  haveI := hν.sigmaFinite
  refine
    ⟨fun n => hμ.set n.unpair.1 ×ˢ hν.set n.unpair.2, fun n =>
      mem_image2_of_mem (hμ.set_mem _) (hν.set_mem _), fun n => ?_, ?_⟩
  · rw [prod_prod]
    exact mul_lt_top (hμ.finite _) (hν.finite _)
  · simp_rw [iUnion_unpair_prod, hμ.spanning, hν.spanning, 

中文:
定义 FiniteSpanningSetsIn.乘积
  签名: {ν : 测度 β} {C : 集合 (集合 α)} {D : 集合 (集合 β)}
  定义体: by
  haveI := hν.sigmaFinite
  refine
    ⟨fun n => hμ.set n.unpair.1 ×ˢ hν.set n.unpair.2, fun n =>
      mem_image2_of_mem (hμ.set_mem _) (hν.set_mem _), fun n => ?_, ?_⟩
  · rw [prod_prod]
    exact mul_lt_top (hμ.finite _) (hν.finite _)
  · simp_rw [iUnion_unpair_prod, hμ.spanning, hν.spanning, 

Depends on / 依赖: finite, iUnion_unpair_prod, mem_image2_of_mem, mul_lt_top, n.unpair, prod_prod, set_mem, sigmaFinite, simp_rw, spanning, univ_prod_univ, unpair
-/
noncomputable def FiniteSpanningSetsIn.prod {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hμ : μ.FiniteSpanningSetsIn C) (hν : ν.FiniteSpanningSetsIn D) :
    (μ.prod ν).FiniteSpanningSetsIn (image2 (· ×ˢ ·) C D) := by
  haveI := hν.sigmaFinite
  refine
    ⟨fun n => hμ.set n.unpair.1 ×ˢ hν.set n.unpair.2, fun n =>
      mem_image2_of_mem (hμ.set_mem _) (hν.set_mem _), fun n => ?_, ?_⟩
  · rw [prod_prod]
    exact mul_lt_top (hμ.finite _) (hν.finite _)
  · simp_rw [iUnion_unpair_prod, hμ.spanning, hν.spanning, univ_prod_univ]

/--
lemma `prod_sum_left` / 引理 `prod_sum_left`

English:
lemma prod_sum_left
  given: {ι : Type*} (m : ι -> Measure α) (μ : Measure β) [SFinite μ]
  proof: by
  ext s hs
  simp only [prod_apply hs, lintegral_sum_measure, hs, sum_apply]

中文:
引理 prod_sum_left
  条件: {ι : 类型} (m : ι -> 测度 α) (μ : 测度 β) [SFinite μ]
  证明: by
  ext s hs
  simp only [prod_apply hs, lintegral_sum_measure, hs, sum_apply]

Depends on / 依赖: lintegral_sum_measure, prod_apply, sum_apply
-/
lemma prod_sum_left {ι : Type*} (m : ι -> Measure α) (μ : Measure β) [SFinite μ] :
    (Measure.sum m).prod μ = Measure.sum (fun i => (m i).prod μ) := by
  ext s hs
  simp only [prod_apply hs, lintegral_sum_measure, hs, sum_apply]

/--
lemma `prod_sum_right` / 引理 `prod_sum_right`

English:
lemma prod_sum_right
  statement: {ι' : Type*} [Countable ι'] (m : Measure α) (m' : ι' -> Measure β)
  proof: by
  ext s hs
  simp only [prod_apply hs, hs, sum_apply]
  have M : forall x, MeasurableSet (Prod.mk x ⁻¹' s) := fun x => measurable_prodMk_left hs
  simp_rw [Measure.sum_apply _ (M _)]
  rw [lintegral_tsum (fun i => (measurable_measure_prodMk_left hs).aemeasurable)]

中文:
引理 prod_sum_right
  结论: {ι' : 类型} [可数 ι'] (m : 测度 α) (m' : ι' -> 测度 β)
  证明: by
  ext s hs
  simp only [prod_apply hs, hs, sum_apply]
  have M : forall x, MeasurableSet (Prod.mk x ⁻¹' s) := fun x => measurable_prodMk_left hs
  simp_rw [Measure.sum_apply _ (M _)]
  rw [lintegral_tsum (fun i => (measurable_measure_prodMk_left hs).aemeasurable)]

Depends on / 依赖: MeasurableSet, Measure, Measure.sum_apply, Prod.mk, aemeasurable, lintegral_tsum, measurable_measure_prodMk_left, measurable_prodMk_left, prod_apply, simp_rw, sum_apply
-/
lemma prod_sum_right {ι' : Type*} [Countable ι'] (m : Measure α) (m' : ι' -> Measure β)
    [forall n, SFinite (m' n)] :
    m.prod (Measure.sum m') = Measure.sum (fun p => m.prod (m' p)) := by
  ext s hs
  simp only [prod_apply hs, hs, sum_apply]
  have M : forall x, MeasurableSet (Prod.mk x ⁻¹' s) := fun x => measurable_prodMk_left hs
  simp_rw [Measure.sum_apply _ (M _)]
  rw [lintegral_tsum (fun i => (measurable_measure_prodMk_left hs).aemeasurable)]

/--
lemma `prod_sum` / 引理 `prod_sum`

English:
lemma prod_sum
  statement: {ι ι' : Type*} [Countable ι'] (m : ι -> Measure α) (m' : ι' -> Measure β)
  proof: by
  simp_rw [prod_sum_left, prod_sum_right, sum_sum]

中文:
引理 prod_sum
  结论: {ι ι' : 类型} [可数 ι'] (m : ι -> 测度 α) (m' : ι' -> 测度 β)
  证明: by
  simp_rw [prod_sum_left, prod_sum_right, sum_sum]

Depends on / 依赖: prod_sum_left, prod_sum_right, simp_rw, sum_sum
-/
lemma prod_sum {ι ι' : Type*} [Countable ι'] (m : ι -> Measure α) (m' : ι' -> Measure β)
    [forall n, SFinite (m' n)] :
    (Measure.sum m).prod (Measure.sum m') =
      Measure.sum (fun (p : ι × ι') => (m p.1).prod (m' p.2)) := by
  simp_rw [prod_sum_left, prod_sum_right, sum_sum]

/--
Instance `prod.instSigmaFinite` / 实例 `prod.instSigmaFinite`

English:
instance prod.instSigmaFinite
  signature: {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
  body: (μ.toFiniteSpanningSetsIn.prod ν.toFiniteSpanningSetsIn).sigmaFinite

中文:
实例 乘积.instSigmaFinite
  签名: {α β : 类型} {_ : 可测空间 α} {μ : 测度 α}
  定义体: (μ.toFiniteSpanningSetsIn.prod ν.toFiniteSpanningSetsIn).sigmaFinite

Depends on / 依赖: sigmaFinite, toFiniteSpanningSetsIn, toFiniteSpanningSetsIn.prod
-/
instance prod.instSigmaFinite {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {_ : MeasurableSpace β} {ν : Measure β} [SigmaFinite ν] :
    SigmaFinite (μ.prod ν) :=
  (μ.toFiniteSpanningSetsIn.prod ν.toFiniteSpanningSetsIn).sigmaFinite

/--
Instance `prod.instSFinite` / 实例 `prod.instSFinite`

English:
instance prod.instSFinite
  signature: {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
  body: by
  have : μ.prod ν =
      Measure.sum (fun (p : Nat × Nat) => (sfiniteSeq μ p.1).prod (sfiniteSeq ν p.2)) := by
    conv_lhs => rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν]
    apply prod_sum
  rw [this]
  infer_instance

中文:
实例 乘积.instSFinite
  签名: {α β : 类型} {_ : 可测空间 α} {μ : 测度 α}
  定义体: by
  have : μ.prod ν =
      Measure.sum (fun (p : Nat × Nat) => (sfiniteSeq μ p.1).prod (sfiniteSeq ν p.2)) := by
    conv_lhs => rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν]
    apply prod_sum
  rw [this]
  infer_instance

Depends on / 依赖: Measure, Measure.sum, conv_lhs, infer_instance, prod_sum, sfiniteSeq, sum_sfiniteSeq
-/
instance prod.instSFinite {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {_ : MeasurableSpace β} {ν : Measure β} [SFinite ν] :
    SFinite (μ.prod ν) := by
  have : μ.prod ν =
      Measure.sum (fun (p : Nat × Nat) => (sfiniteSeq μ p.1).prod (sfiniteSeq ν p.2)) := by
    conv_lhs => rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν]
    apply prod_sum
  rw [this]
  infer_instance

instance {α β} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    [MeasureSpace β] [SigmaFinite (volume : Measure β)] : SigmaFinite (volume : Measure (α × β)) :=
  prod.instSigmaFinite

instance {α β} [MeasureSpace α] [SFinite (volume : Measure α)]
    [MeasureSpace β] [SFinite (volume : Measure β)] : SFinite (volume : Measure (α × β)) :=
  prod.instSFinite

/--
theorem `prod_eq_generateFrom` / 定理 `prod_eq_generateFrom`

English:
theorem prod_eq_generateFrom
  statement: {μ : Measure α} {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
  proof: by
  refine
    (h3C.prod h3D).ext
      (generateFrom_eq_prod hC hD h3C.isCountablySpanning h3D.isCountablySpanning).symm
      (h2C.prod h2D) ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  have := h3D.sigmaFinite
  rw [h₁ s hs t ht]; rw [prod_prod]

中文:
定理 prod_eq_generateFrom
  结论: {μ : 测度 α} {ν : 测度 β} {C : 集合 (集合 α)} {D : 集合 (集合 β)}
  证明: by
  refine
    (h3C.prod h3D).ext
      (generateFrom_eq_prod hC hD h3C.isCountablySpanning h3D.isCountablySpanning).symm
      (h2C.prod h2D) ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  have := h3D.sigmaFinite
  rw [h₁ s hs t ht]; rw [prod_prod]

Depends on / 依赖: generateFrom_eq_prod, h2C.prod, h3C.isCountablySpanning, h3C.prod, h3D.isCountablySpanning, h3D.sigmaFinite, isCountablySpanning, prod_prod, sigmaFinite
-/
theorem prod_eq_generateFrom {μ : Measure α} {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hC : generateFrom C = ‹_›) (hD : generateFrom D = ‹_›) (h2C : IsPiSystem C)
    (h2D : IsPiSystem D) (h3C : μ.FiniteSpanningSetsIn C) (h3D : ν.FiniteSpanningSetsIn D)
    {μν : Measure (α × β)} (h₁ : forall s in C, forall t in D, μν (s ×ˢ t) = μ s * ν t) : μ.prod ν = μν := by
  refine
    (h3C.prod h3D).ext
      (generateFrom_eq_prod hC hD h3C.isCountablySpanning h3D.isCountablySpanning).symm
      (h2C.prod h2D) ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  have := h3D.sigmaFinite
  rw [h₁ s hs t ht]; rw [prod_prod]

/- Note that the next theorem is not true for s-finite measures: let `μ = ν = ∞ • Leb` on `[0,1]`
(they are s-finite as countable sums of the finite Lebesgue measure), and let `μν = μ.prod ν + λ`
where `λ` is Lebesgue measure on the diagonal. Then both measures give infinite mass to rectangles
`s × t` whose sides have positive Lebesgue measure, and `0` measure when one of the sides has zero
Lebesgue measure. And yet they do not coincide, as the first one gives zero mass to the diagonal,
and the second one gives mass one.
-/
/--
theorem `prod_eq` / 定理 `prod_eq`

English:
theorem prod_eq
  statement: {μ : Measure α} [SigmaFinite μ] {ν : Measure β} [SigmaFinite ν]
  proof: prod_eq_generateFrom generateFrom_measurableSet generateFrom_measurableSet
    isPiSystem_measurableSet isPiSystem_measurableSet μ.toFiniteSpanningSetsIn
    ν.toFiniteSpanningSetsIn fun s hs t ht => h s t hs ht

中文:
定理 prod_eq
  结论: {μ : 测度 α} [σ有限 μ] {ν : 测度 β} [σ有限 ν]
  证明: prod_eq_generateFrom generateFrom_measurableSet generateFrom_measurableSet
    isPiSystem_measurableSet isPiSystem_measurableSet μ.toFiniteSpanningSetsIn
    ν.toFiniteSpanningSetsIn fun s hs t ht => h s t hs ht

Depends on / 依赖: generateFrom_measurableSet, isPiSystem_measurableSet, prod_eq_generateFrom, toFiniteSpanningSetsIn
-/
theorem prod_eq {μ : Measure α} [SigmaFinite μ] {ν : Measure β} [SigmaFinite ν]
    {μν : Measure (α × β)}
    (h : forall s t, MeasurableSet s -> MeasurableSet t -> μν (s ×ˢ t) = μ s * ν t) : μ.prod ν = μν :=
  prod_eq_generateFrom generateFrom_measurableSet generateFrom_measurableSet
    isPiSystem_measurableSet isPiSystem_measurableSet μ.toFiniteSpanningSetsIn
    ν.toFiniteSpanningSetsIn fun s hs t ht => h s t hs ht

-- This is not true for σ-finite measures. See the discussion at
-- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Uniqueness.20of.20sigma-finite.20measures.20on.20a.20product.20space/with/541741071
/--
lemma `ext_prod` / 引理 `ext_prod`

English:
lemma ext_prod
  statement: {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  proof: by
  ext s hs
  have h_univ : μ univ = ν univ := by
    rw [← univ_prod_univ]
    exact h .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod (by simp)
    ?_ ?_ ?_ s hs
  · rintro - ⟨s, hs, t, ht, rfl⟩
   

中文:
引理 ext_prod
  结论: {α β : 类型} {mα : 可测空间 α} {mβ : 可测空间 β}
  证明: by
  ext s hs
  have h_univ : μ univ = ν univ := by
    rw [← univ_prod_univ]
    exact h .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod (by simp)
    ?_ ?_ ?_ s hs
  · rintro - ⟨s, hs, t, ht, rfl⟩
   

Depends on / 依赖: IsFiniteMeasure, MeasurableSpace, MeasurableSpace.induction_on_inter, generateFrom_prod, generateFrom_prod.symm, h_disj, h_eq, h_univ, induction_on_inter, isPiSystem_prod, measure_compl, measure_iUnion, measure_ne_top, simp_rw, univ_prod_univ
-/
lemma ext_prod {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ ν : Measure (α × β)} [IsFiniteMeasure μ]
    (h : forall {s : Set α} {t : Set β}, MeasurableSet s -> MeasurableSet t -> μ (s ×ˢ t) = ν (s ×ˢ t)) :
    μ = ν := by
  ext s hs
  have h_univ : μ univ = ν univ := by
    rw [← univ_prod_univ]
    exact h .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod (by simp)
    ?_ ?_ ?_ s hs
  · rintro - ⟨s, hs, t, ht, rfl⟩
    exact h hs ht
  · intro t ht h
    simp_rw [measure_compl ht (measure_ne_top _ _), h, h_univ]
  · intro f h_disj hf h_eq
    simp_rw [measure_iUnion h_disj hf, h_eq]

/--
lemma `ext_prod_iff` / 引理 `ext_prod_iff`

English:
lemma ext_prod_iff
  statement: {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  proof: ⟨fun h s t hs ht => by rw [h], Measure.ext_prod⟩

中文:
引理 ext_prod_iff
  结论: {α β : 类型} {mα : 可测空间 α} {mβ : 可测空间 β}
  证明: ⟨fun h s t hs ht => by rw [h], Measure.ext_prod⟩

Depends on / 依赖: Measure, Measure.ext_prod, ext_prod
-/
lemma ext_prod_iff {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ ν : Measure (α × β)} [IsFiniteMeasure μ] :
    μ = ν
      ↔ forall {s : Set α} {t : Set β}, MeasurableSet s -> MeasurableSet t -> μ (s ×ˢ t) = ν (s ×ˢ t) :=
  ⟨fun h s t hs ht => by rw [h], Measure.ext_prod⟩

/--
lemma `ext_prod₃` / 引理 `ext_prod₃`

English:
lemma ext_prod₃
  statement: {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  proof: by
  ext s hs
  have h_univ : μ univ = ν univ := by
    simp_rw [← univ_prod_univ]
    exact h .univ .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  let C₂ := image2 (· ×ˢ ·) { t : Set β | MeasurableSet t } { u : Set γ | MeasurableSet u }
  let C := image2 (· ×ˢ ·) { s : Set α | Mea

中文:
引理 ext_prod₃
  结论: {α β γ : 类型} {mα : 可测空间 α} {mβ : 可测空间 β}
  证明: by
  ext s hs
  have h_univ : μ univ = ν univ := by
    simp_rw [← univ_prod_univ]
    exact h .univ .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  let C₂ := image2 (· ×ˢ ·) { t : Set β | MeasurableSet t } { u : Set γ | MeasurableSet u }
  let C := image2 (· ×ˢ ·) { s : Set α | Mea

Depends on / 依赖: IsFiniteMeasure, MeasurableSet, MeasurableSpace, MeasurableSpace.induction_on_inter, generateFrom_eq_prod, generateFrom_prod, h_univ, image2, induction_on_inter, isCountably, simp_rw, univ_prod_univ
-/
lemma ext_prod₃ {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ]
    (h : forall {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s -> MeasurableSet t -> MeasurableSet u -> μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :
    μ = ν := by
  ext s hs
  have h_univ : μ univ = ν univ := by
    simp_rw [← univ_prod_univ]
    exact h .univ .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  let C₂ := image2 (· ×ˢ ·) { t : Set β | MeasurableSet t } { u : Set γ | MeasurableSet u }
  let C := image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } C₂
  refine MeasurableSpace.induction_on_inter (s := C) ?_ ?_ (by simp) ?_ ?_ ?_ s hs
  · refine (generateFrom_eq_prod (C := { s : Set α | MeasurableSet s }) (D := C₂) (by simp)
      generateFrom_prod isCountablySpanning_measurableSet ?_).symm
    exact isCountablySpanning_measurableSet.prod isCountablySpanning_measurableSet
  · exact MeasurableSpace.isPiSystem_measurableSet.prod isPiSystem_prod
  · rintro - ⟨s, hs, -, ⟨t, ht, u, hu, rfl⟩, rfl⟩
    exact h hs ht hu
  · intro t ht h
    simp_rw [measure_compl ht (measure_ne_top _ _), h, h_univ]
  · intro f h_disj hf h_eq
    simp_rw [measure_iUnion h_disj hf, h_eq]

/--
lemma `ext_prod₃_iff` / 引理 `ext_prod₃_iff`

English:
lemma ext_prod₃_iff
  statement: {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  proof: ⟨fun h s t u hs ht hu => by rw [h], Measure.ext_prod₃⟩

中文:
引理 ext_prod₃_iff
  结论: {α β γ : 类型} {mα : 可测空间 α} {mβ : 可测空间 β}
  证明: ⟨fun h s t u hs ht hu => by rw [h], Measure.ext_prod₃⟩

Depends on / 依赖: Measure, Measure.ext_prod
-/
lemma ext_prod₃_iff {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ] :
    μ = ν ↔ (forall {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s -> MeasurableSet t -> MeasurableSet u -> μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :=
  ⟨fun h s t u hs ht hu => by rw [h], Measure.ext_prod₃⟩

/--
lemma `ext_prod₃_iff'` / 引理 `ext_prod₃_iff'`

English:
lemma ext_prod₃_iff'
  statement: {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  proof: by
  rw [← MeasurableEquiv.prodAssoc.map_measurableEquiv_injective.eq_iff]; rw [ext_prod₃_iff]
  have h_eq (ν : Measure ((α × β) × γ)) {s : Set α} {t : Set β} {u : Set γ}
      (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) :
      ν.map MeasurableEquiv.prodAssoc (s ×ˢ (t ×ˢ u)

中文:
引理 ext_prod₃_iff'
  结论: {α β γ : 类型} {mα : 可测空间 α} {mβ : 可测空间 β}
  证明: by
  rw [← MeasurableEquiv.prodAssoc.map_measurableEquiv_injective.eq_iff]; rw [ext_prod₃_iff]
  have h_eq (ν : Measure ((α × β) × γ)) {s : Set α} {t : Set β} {u : Set γ}
      (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) :
      ν.map MeasurableEquiv.prodAssoc (s ×ˢ (t ×ˢ u)

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodAssoc.map_measurableEquiv_injective.eq_iff, MeasurableSet, Measure, eq_iff, fun_prop, h_eq, hs.prod, ht.prod, map_apply, map_measurableEquiv_injective, prodAssoc, specialize
-/
lemma ext_prod₃_iff' {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure ((α × β) × γ)} [IsFiniteMeasure μ] :
    μ = ν ↔ (forall {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s -> MeasurableSet t -> MeasurableSet u ->
      μ ((s ×ˢ t) ×ˢ u) = ν ((s ×ˢ t) ×ˢ u)) := by
  rw [← MeasurableEquiv.prodAssoc.map_measurableEquiv_injective.eq_iff]; rw [ext_prod₃_iff]
  have h_eq (ν : Measure ((α × β) × γ)) {s : Set α} {t : Set β} {u : Set γ}
      (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) :
      ν.map MeasurableEquiv.prodAssoc (s ×ˢ (t ×ˢ u)) = ν ((s ×ˢ t) ×ˢ u) := by
    rw [map_apply (by fun_prop) (hs.prod (ht.prod hu))]
    congr 1 with x
    simp [MeasurableEquiv.prodAssoc]
  refine ⟨fun h s t u hs ht hu => ?_, fun h s t u hs ht hu => ?_⟩ <;> specialize h hs ht hu
  · rwa [h_eq μ hs ht hu, h_eq ν hs ht hu] at h
  · rwa [h_eq μ hs ht hu, h_eq ν hs ht hu]

/-- Two finite measures on a product `(α × β) × γ` that are equal on products of sets are equal.
See `ext_prod₃` for the same statement for `α × β × γ`. -/
alias ⟨_, ext_prod₃'⟩ := ext_prod₃_iff'

variable [SFinite μ]

/--
theorem `prod_swap` / 定理 `prod_swap`

English:
theorem prod_swap
  statement: map Prod.swap (μ.prod ν) = ν.prod μ
  proof: by
  have : sum (fun (i : Nat × Nat) => map Prod.swap ((sfiniteSeq μ i.1).prod (sfiniteSeq ν i.2)))
       = sum (fun (i : Nat × Nat) => map Prod.swap ((sfiniteSeq μ i.2).prod (sfiniteSeq ν i.1))) := by
    ext s hs
    rw [sum_apply _ hs]; rw [sum_apply _ hs]
    exact ((Equiv.prodComm Nat Nat).tsu

中文:
定理 prod_swap
  结论: map 积类型.swap (μ.乘积 ν) = ν.乘积 μ
  证明: by
  have : sum (fun (i : Nat × Nat) => map Prod.swap ((sfiniteSeq μ i.1).prod (sfiniteSeq ν i.2)))
       = sum (fun (i : Nat × Nat) => map Prod.swap ((sfiniteSeq μ i.2).prod (sfiniteSeq ν i.1))) := by
    ext s hs
    rw [sum_apply _ hs]; rw [sum_apply _ hs]
    exact ((Equiv.prodComm Nat Nat).tsu

Depends on / 依赖: Equiv.prodComm, Prod.swap, aemeasurable, map_apply, map_sum, measurable_swap, measurable_swap.aemeasurable, prodComm, prod_eq, prod_sum, sfiniteSeq, simp_rw, sum_apply, sum_sfiniteSeq, tsum_eq
-/
theorem prod_swap : map Prod.swap (μ.prod ν) = ν.prod μ := by
  have : sum (fun (i : Nat × Nat) => map Prod.swap ((sfiniteSeq μ i.1).prod (sfiniteSeq ν i.2)))
       = sum (fun (i : Nat × Nat) => map Prod.swap ((sfiniteSeq μ i.2).prod (sfiniteSeq ν i.1))) := by
    ext s hs
    rw [sum_apply _ hs]; rw [sum_apply _ hs]
    exact ((Equiv.prodComm Nat Nat).tsum_eq _).symm
  rw [← sum_sfiniteSeq μ]; rw [← sum_sfiniteSeq ν]; rw [prod_sum]; rw [prod_sum]; rw [map_sum measurable_swap.aemeasurable]; rw [this]
  congr 1
  ext1 i
  refine (prod_eq ?_).symm
  intro s t hs ht
  simp_rw [map_apply measurable_swap (hs.prod ht), preimage_swap_prod, prod_prod, mul_comm]

/--
theorem `measurePreserving_swap` / 定理 `measurePreserving_swap`

English:
theorem measurePreserving_swap
  statement: MeasurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
  proof: ⟨measurable_swap, prod_swap⟩

中文:
定理 measurePreserving_swap
  结论: 保测 积类型.swap (μ.乘积 ν) (ν.乘积 μ)
  证明: ⟨measurable_swap, prod_swap⟩

Depends on / 依赖: measurable_swap, prod_swap
-/
theorem measurePreserving_swap : MeasurePreserving Prod.swap (μ.prod ν) (ν.prod μ) :=
  ⟨measurable_swap, prod_swap⟩

/--
theorem `prod_apply_symm` / 定理 `prod_apply_symm`

English:
theorem prod_apply_symm
  given: {s : Set (α × β)} (hs : MeasurableSet s)
  proof: by
  rw [← prod_swap]; rw [map_apply measurable_swap hs]; rw [prod_apply (measurable_swap hs)]
  rfl

中文:
定理 prod_apply_symm
  条件: {s : 集合 (α × β)} (hs : 可测集 s)
  证明: by
  rw [← prod_swap]; rw [map_apply measurable_swap hs]; rw [prod_apply (measurable_swap hs)]
  rfl

Depends on / 依赖: map_apply, measurable_swap, prod_apply, prod_swap
-/
theorem prod_apply_symm {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν := by
  rw [← prod_swap]; rw [map_apply measurable_swap hs]; rw [prod_apply (measurable_swap hs)]
  rfl

/--
theorem `ae_ae_comm` / 定理 `ae_ae_comm`

English:
theorem ae_ae_comm
  given: {p : α -> β -> Prop} (h : MeasurableSet {x : α × β | p x.1 x.2})
  proof: calc
_ ↔ forallᵐ x ∂μ.prod ν, p x.1 x.2 := .symm ae_prod_iff_ae_ae h
  _ ↔ forallᵐ x ∂ν.prod μ, p x.2 x.1 := by rw [← prod_swap, ae_map_iff (by fun_prop) h]; simp
_ ↔ forallᵐ y ∂ν, forallᵐ x ∂μ, p x y := ae_prod_iff_ae_ae measurable_swap h

中文:
定理 ae_ae_comm
  条件: {p : α -> β -> 命题} (h : 可测集 {x : α × β | p x.1 x.2})
  证明: calc
_ ↔ forallᵐ x ∂μ.prod ν, p x.1 x.2 := .symm ae_prod_iff_ae_ae h
  _ ↔ forallᵐ x ∂ν.prod μ, p x.2 x.1 := by rw [← prod_swap, ae_map_iff (by fun_prop) h]; simp
_ ↔ forallᵐ y ∂ν, forallᵐ x ∂μ, p x y := ae_prod_iff_ae_ae measurable_swap h
-/
theorem ae_ae_comm {p : α -> β -> Prop} (h : MeasurableSet {x : α × β | p x.1 x.2}) :
    (forallᵐ x ∂μ, forallᵐ y ∂ν, p x y) ↔ forallᵐ y ∂ν, forallᵐ x ∂μ, p x y := calc
_ ↔ forallᵐ x ∂μ.prod ν, p x.1 x.2 := .symm ae_prod_iff_ae_ae h
  _ ↔ forallᵐ x ∂ν.prod μ, p x.2 x.1 := by rw [← prod_swap, ae_map_iff (by fun_prop) h]; simp
_ ↔ forallᵐ y ∂ν, forallᵐ x ∂μ, p x y := ae_prod_iff_ae_ae measurable_swap h

/--
lemma `_root_.MeasureTheory.NullMeasurableSet.left_of_prod` / 引理 `_root_.MeasureTheory.NullMeasurableSet.left_of_prod`

English:
lemma _root_.MeasureTheory.NullMeasurableSet.left_of_prod
  statement: {s : Set α} {t : Set β}
  proof: by
  refine .right_of_prod ?_ ht
  rw [← preimage_swap_prod]
  exact h.preimage measurePreserving_swap.quasiMeasurePreserving

中文:
引理 _root_.测度论.NullMeasurableSet.left_of_prod
  结论: {s : 集合 α} {t : 集合 β}
  证明: by
  refine .right_of_prod ?_ ht
  rw [← preimage_swap_prod]
  exact h.preimage measurePreserving_swap.quasiMeasurePreserving

Depends on / 依赖: Subtype, Subtype.val, congr_arg, h.preimage, measurePreserving_swap, measurePreserving_swap.quasiMeasurePreserving, mk_bot, preimage, preimage_swap_prod, quasiMeasurePreserving, right_of_prod
-/
lemma _root_.MeasureTheory.NullMeasurableSet.left_of_prod {s : Set α} {t : Set β}
    (h : NullMeasurableSet (s ×ˢ t) (μ.prod ν)) (ht : ν t != 0) : NullMeasurableSet s μ := by
  refine .right_of_prod ?_ ht
  rw [← preimage_swap_prod]
  exact h.preimage measurePreserving_swap.quasiMeasurePreserving

/--
lemma `_root_.MeasureTheory.NullMeasurableSet.of_preimage_fst` / 引理 `_root_.MeasureTheory.NullMeasurableSet.of_preimage_fst`

English:
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_fst
  statement: [NeZero ν] {s : Set α}
  proof: .left_of_prod (by rwa [prod_univ]) (NeZero.ne (ν univ))

中文:
引理 _root_.测度论.NullMeasurableSet.of_preimage_fst
  结论: [NeZero ν] {s : 集合 α}
  证明: .left_of_prod (by rwa [prod_univ]) (NeZero.ne (ν univ))

Depends on / 依赖: NeZero, NeZero.ne, left_of_prod, prod_univ
-/
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_fst [NeZero ν] {s : Set α}
    (h : NullMeasurableSet (Prod.fst ⁻¹' s) (μ.prod ν)) : NullMeasurableSet s μ :=
  .left_of_prod (by rwa [prod_univ]) (NeZero.ne (ν univ))

/--
lemma `nullMeasurableSet_preimage_fst` / 引理 `nullMeasurableSet_preimage_fst`

English:
lemma nullMeasurableSet_preimage_fst
  given: [NeZero ν] {s : Set α}
  proof: ⟨.of_preimage_fst, (.preimage · quasiMeasurePreserving_fst)⟩

中文:
引理 nullMeasurableSet_preimage_fst
  条件: [NeZero ν] {s : 集合 α}
  证明: ⟨.of_preimage_fst, (.preimage · quasiMeasurePreserving_fst)⟩

Depends on / 依赖: of_preimage_fst, preimage, quasiMeasurePreserving_fst
-/
lemma nullMeasurableSet_preimage_fst [NeZero ν] {s : Set α} :
    NullMeasurableSet (Prod.fst ⁻¹' s) (μ.prod ν) ↔ NullMeasurableSet s μ :=
  ⟨.of_preimage_fst, (.preimage · quasiMeasurePreserving_fst)⟩

/--
lemma `nullMeasurable_comp_fst` / 引理 `nullMeasurable_comp_fst`

English:
lemma nullMeasurable_comp_fst
  given: [NeZero ν] {f : α -> γ}
  proof: forall₂_congr fun s _ => nullMeasurableSet_preimage_fst (s := f ⁻¹' s)

中文:
引理 nullMeasurable_comp_fst
  条件: [NeZero ν] {f : α -> γ}
  证明: forall₂_congr fun s _ => nullMeasurableSet_preimage_fst (s := f ⁻¹' s)

Depends on / 依赖: nullMeasurableSet_preimage_fst
-/
lemma nullMeasurable_comp_fst [NeZero ν] {f : α -> γ} :
    NullMeasurable (f ∘ Prod.fst) (μ.prod ν) ↔ NullMeasurable f μ :=
  forall₂_congr fun s _ => nullMeasurableSet_preimage_fst (s := f ⁻¹' s)

/--
lemma `nullMeasurableSet_prod_of_ne_zero` / 引理 `nullMeasurableSet_prod_of_ne_zero`

English:
lemma nullMeasurableSet_prod_of_ne_zero
  given: {s : Set α} {t : Set β} (hs : μ s != 0) (ht : ν t != 0)
  proof: ⟨fun h => ⟨h.left_of_prod ht, h.right_of_prod hs⟩, fun ⟨hs, ht⟩ => hs.prod ht⟩

中文:
引理 nullMeasurableSet_prod_of_ne_zero
  条件: {s : 集合 α} {t : 集合 β} (hs : μ s != 0) (ht : ν t != 0)
  证明: ⟨fun h => ⟨h.left_of_prod ht, h.right_of_prod hs⟩, fun ⟨hs, ht⟩ => hs.prod ht⟩

Depends on / 依赖: h.left_of_prod, h.right_of_prod, hs.prod, left_of_prod, right_of_prod
-/
lemma nullMeasurableSet_prod_of_ne_zero {s : Set α} {t : Set β} (hs : μ s != 0) (ht : ν t != 0) :
    NullMeasurableSet (s ×ˢ t) (μ.prod ν) ↔ NullMeasurableSet s μ ∧ NullMeasurableSet t ν :=
  ⟨fun h => ⟨h.left_of_prod ht, h.right_of_prod hs⟩, fun ⟨hs, ht⟩ => hs.prod ht⟩

/--
lemma `nullMeasurableSet_prod` / 引理 `nullMeasurableSet_prod`

English:
lemma nullMeasurableSet_prod
  given: {s : Set α} {t : Set β}
  proof: by
  rcases eq_or_ne (μ s) 0 with hs | hs; · simp [NullMeasurableSet.of_null, *]
  rcases eq_or_ne (ν t) 0 with ht | ht; · simp [NullMeasurableSet.of_null, *]
  simp [*, nullMeasurableSet_prod_of_ne_zero]

中文:
引理 nullMeasurableSet_prod
  条件: {s : 集合 α} {t : 集合 β}
  证明: by
  rcases eq_or_ne (μ s) 0 with hs | hs; · simp [NullMeasurableSet.of_null, *]
  rcases eq_or_ne (ν t) 0 with ht | ht; · simp [NullMeasurableSet.of_null, *]
  simp [*, nullMeasurableSet_prod_of_ne_zero]

Depends on / 依赖: NullMeasurableSet, NullMeasurableSet.of_null, eq_or_ne, nullMeasurableSet_prod_of_ne_zero, of_null
-/
lemma nullMeasurableSet_prod {s : Set α} {t : Set β} :
    NullMeasurableSet (s ×ˢ t) (μ.prod ν) ↔
      NullMeasurableSet s μ ∧ NullMeasurableSet t ν ∨ μ s = 0 ∨ ν t = 0 := by
  rcases eq_or_ne (μ s) 0 with hs | hs; · simp [NullMeasurableSet.of_null, *]
  rcases eq_or_ne (ν t) 0 with ht | ht; · simp [NullMeasurableSet.of_null, *]
  simp [*, nullMeasurableSet_prod_of_ne_zero]

/--
theorem `prodAssoc_prod` / 定理 `prodAssoc_prod`

English:
theorem prodAssoc_prod
  given: [SFinite τ]
  proof: by
  have : sum (fun (p : Nat × Nat × Nat) =>
        (sfiniteSeq μ p.1).prod ((sfiniteSeq ν p.2.1).prod (sfiniteSeq τ p.2.2)))
      = sum (fun (p : (Nat × Nat) × Nat) =>
        (sfiniteSeq μ p.1.1).prod ((sfiniteSeq ν p.1.2).prod (sfiniteSeq τ p.2))) := by
    ext s hs
    rw [sum_apply _ hs]; rw

中文:
定理 prodAssoc_prod
  条件: [SFinite τ]
  证明: by
  have : sum (fun (p : Nat × Nat × Nat) =>
        (sfiniteSeq μ p.1).prod ((sfiniteSeq ν p.2.1).prod (sfiniteSeq τ p.2.2)))
      = sum (fun (p : (Nat × Nat) × Nat) =>
        (sfiniteSeq μ p.1.1).prod ((sfiniteSeq ν p.1.2).prod (sfiniteSeq τ p.2))) := by
    ext s hs
    rw [sum_apply _ hs]; rw

Depends on / 依赖: Equiv.prodAssoc, Equiv.prodAssoc_apply, MeasurableEquiv, MeasurableEquiv.prodAss, map_sum, prodAss, prodAssoc, prodAssoc_apply, prod_sum, sfiniteSeq, sum_apply, sum_sfiniteSeq, tsum_eq
-/
theorem prodAssoc_prod [SFinite τ] :
    map MeasurableEquiv.prodAssoc ((μ.prod ν).prod τ) = μ.prod (ν.prod τ) := by
  have : sum (fun (p : Nat × Nat × Nat) =>
        (sfiniteSeq μ p.1).prod ((sfiniteSeq ν p.2.1).prod (sfiniteSeq τ p.2.2)))
      = sum (fun (p : (Nat × Nat) × Nat) =>
        (sfiniteSeq μ p.1.1).prod ((sfiniteSeq ν p.1.2).prod (sfiniteSeq τ p.2))) := by
    ext s hs
    rw [sum_apply _ hs]; rw [sum_apply _ hs]; rw [← (Equiv.prodAssoc _ _ _).tsum_eq]
    simp only [Equiv.prodAssoc_apply]
  rw [← sum_sfiniteSeq μ]; rw [← sum_sfiniteSeq ν]; rw [← sum_sfiniteSeq τ]; rw [prod_sum]; rw [prod_sum]; rw [map_sum MeasurableEquiv.prodAssoc.measurable.aemeasurable]; rw [prod_sum]; rw [prod_sum]; rw [this]
  congr
  ext1 i
  refine (prod_eq_generateFrom generateFrom_measurableSet generateFrom_prod
    isPiSystem_measurableSet isPiSystem_prod ((sfiniteSeq μ i.1.1)).toFiniteSpanningSetsIn
    ((sfiniteSeq ν i.1.2).toFiniteSpanningSetsIn.prod (sfiniteSeq τ i.2).toFiniteSpanningSetsIn)
      ?_).symm
  rintro s hs _ ⟨t, ht, u, hu, rfl⟩; rw [mem_ofPred_eq] at hs ht hu
  simp_rw [map_apply (MeasurableEquiv.measurable _) (hs.prod (ht.prod hu)),
    MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prod_assoc_preimage, prod_prod,
    mul_assoc]


/--
theorem `prod_restrict` / 定理 `prod_restrict`

English:
theorem prod_restrict
  given: (s : Set α) (t : Set β)
  proof: by
  rw [← sum_sfiniteSeq μ]; rw [← sum_sfiniteSeq ν]; rw [restrict_sum_of_countable]; rw [restrict_sum_of_countable]; rw [prod_sum]; rw [prod_sum]; rw [restrict_sum_of_countable]
  congr 1
  ext1 i
  refine prod_eq fun s' t' hs' ht' => ?_
  rw [restrict_apply (hs'.prod ht')]; rw [prod_inter_prod]; 

中文:
定理 prod_restrict
  条件: (s : 集合 α) (t : 集合 β)
  证明: by
  rw [← sum_sfiniteSeq μ]; rw [← sum_sfiniteSeq ν]; rw [restrict_sum_of_countable]; rw [restrict_sum_of_countable]; rw [prod_sum]; rw [prod_sum]; rw [restrict_sum_of_countable]
  congr 1
  ext1 i
  refine prod_eq fun s' t' hs' ht' => ?_
  rw [restrict_apply (hs'.prod ht')]; rw [prod_inter_prod]; 

Depends on / 依赖: prod_eq, prod_inter_prod, prod_prod, prod_sum, restrict_apply, restrict_sum_of_countable, sum_sfiniteSeq
-/
theorem prod_restrict (s : Set α) (t : Set β) :
    (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) := by
  rw [← sum_sfiniteSeq μ]; rw [← sum_sfiniteSeq ν]; rw [restrict_sum_of_countable]; rw [restrict_sum_of_countable]; rw [prod_sum]; rw [prod_sum]; rw [restrict_sum_of_countable]
  congr 1
  ext1 i
  refine prod_eq fun s' t' hs' ht' => ?_
  rw [restrict_apply (hs'.prod ht')]; rw [prod_inter_prod]; rw [prod_prod]; rw [restrict_apply hs']; rw [restrict_apply ht']

/--
theorem `restrict_prod_eq_prod_univ` / 定理 `restrict_prod_eq_prod_univ`

English:
theorem restrict_prod_eq_prod_univ
  given: (s : Set α)
  proof: by
  have : ν = ν.restrict Set.univ := Measure.restrict_univ.symm
  rw [this]; rw [Measure.prod_restrict]; rw [← this]

中文:
定理 restrict_prod_eq_prod_univ
  条件: (s : 集合 α)
  证明: by
  have : ν = ν.restrict Set.univ := Measure.restrict_univ.symm
  rw [this]; rw [Measure.prod_restrict]; rw [← this]

Depends on / 依赖: Measure, Measure.prod_restrict, Measure.restrict_univ.symm, Set.univ, prod_restrict, restrict, restrict_univ
-/
theorem restrict_prod_eq_prod_univ (s : Set α) :
    (μ.restrict s).prod ν = (μ.prod ν).restrict (s ×ˢ univ) := by
  have : ν = ν.restrict Set.univ := Measure.restrict_univ.symm
  rw [this]; rw [Measure.prod_restrict]; rw [← this]

/--
theorem `prod_dirac` / 定理 `prod_dirac`

English:
theorem prod_dirac
  given: (y : β)
  statement: μ.prod (dirac y) = map (fun x => (x, y)) μ
  proof: by
  classical
  rw [← sum_sfiniteSeq μ]; rw [prod_sum_left]; rw [map_sum measurable_prodMk_right.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prodMk_right (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
    dirac_apply' _ ht, ← indicator

中文:
定理 prod_dirac
  条件: (y : β)
  结论: μ.乘积 (dirac y) = map (fun x => (x, y)) μ
  证明: by
  classical
  rw [← sum_sfiniteSeq μ]; rw [prod_sum_left]; rw [map_sum measurable_prodMk_right.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prodMk_right (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
    dirac_apply' _ ht, ← indicator

Depends on / 依赖: Pi.one_apply, aemeasurable, classical, dirac_apply, hs.prod, indicator_mul_right, map_apply, map_sum, measurable_prodMk_right, measurable_prodMk_right.aemeasurable, measure_if, mk_preimage_prod_left_eq_if, mul_one, one_apply, prod_eq, prod_sum_left, sfiniteSeq, simp_rw, sum_sfiniteSeq
-/
theorem prod_dirac (y : β) : μ.prod (dirac y) = map (fun x => (x, y)) μ := by
  classical
  rw [← sum_sfiniteSeq μ]; rw [prod_sum_left]; rw [map_sum measurable_prodMk_right.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prodMk_right (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
    dirac_apply' _ ht, ← indicator_mul_right _ fun _ => sfiniteSeq μ i s, Pi.one_apply, mul_one]

/--
theorem `dirac_prod` / 定理 `dirac_prod`

English:
theorem dirac_prod
  given: (x : α)
  statement: (dirac x).prod ν = map (Prod.mk x) ν
  proof: by
  classical
  rw [← sum_sfiniteSeq ν]; rw [prod_sum_right]; rw [map_sum measurable_prodMk_left.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prodMk_left (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
    dirac_apply' _ hs, ← indicator

中文:
定理 dirac_prod
  条件: (x : α)
  结论: (dirac x).乘积 ν = map (积类型.mk x) ν
  证明: by
  classical
  rw [← sum_sfiniteSeq ν]; rw [prod_sum_right]; rw [map_sum measurable_prodMk_left.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prodMk_left (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
    dirac_apply' _ hs, ← indicator

Depends on / 依赖: Pi.one_apply, aemeasurable, classical, dirac_apply, hs.prod, indicator_mul_left, map_apply, map_sum, measurable_prodMk_left, measurable_prodMk_left.aemeasurable, measure_if, mk_preimage_prod_right_eq_if, one_apply, one_mul, prod_eq, prod_sum_right, sfiniteSeq, simp_rw, sum_sfiniteSeq
-/
theorem dirac_prod (x : α) : (dirac x).prod ν = map (Prod.mk x) ν := by
  classical
  rw [← sum_sfiniteSeq ν]; rw [prod_sum_right]; rw [map_sum measurable_prodMk_left.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prodMk_left (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
    dirac_apply' _ hs, ← indicator_mul_left _ _ fun _ => sfiniteSeq ν i t, Pi.one_apply, one_mul]

/--
theorem `dirac_prod_dirac` / 定理 `dirac_prod_dirac`

English:
theorem dirac_prod_dirac
  given: {x : α} {y : β}
  statement: (dirac x).prod (dirac y) = dirac (x, y)
  proof: by
  rw [prod_dirac]; rw [map_dirac' measurable_prodMk_right]

中文:
定理 dirac_prod_dirac
  条件: {x : α} {y : β}
  结论: (dirac x).乘积 (dirac y) = dirac (x, y)
  证明: by
  rw [prod_dirac]; rw [map_dirac' measurable_prodMk_right]

Depends on / 依赖: map_dirac, measurable_prodMk_right, prod_dirac
-/
theorem dirac_prod_dirac {x : α} {y : β} : (dirac x).prod (dirac y) = dirac (x, y) := by
  rw [prod_dirac]; rw [map_dirac' measurable_prodMk_right]

/--
theorem `prod_add` / 定理 `prod_add`

English:
theorem prod_add
  given: (ν' : Measure β) [SFinite ν']
  statement: μ.prod (ν + ν') = μ.prod ν + μ.prod ν'
  proof: by
  simp_rw [← sum_sfiniteSeq ν, ← sum_sfiniteSeq ν', sum_add_sum, ← sum_sfiniteSeq μ, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, left_distrib]

中文:
定理 prod_add
  条件: (ν' : 测度 β) [SFinite ν']
  结论: μ.乘积 (ν + ν') = μ.乘积 ν + μ.乘积 ν'
  证明: by
  simp_rw [← sum_sfiniteSeq ν, ← sum_sfiniteSeq ν', sum_add_sum, ← sum_sfiniteSeq μ, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, left_distrib]

Depends on / 依赖: add_apply, left_distrib, prod_eq, prod_prod, prod_sum, simp_rw, sum_add_sum, sum_sfiniteSeq
-/
theorem prod_add (ν' : Measure β) [SFinite ν'] : μ.prod (ν + ν') = μ.prod ν + μ.prod ν' := by
  simp_rw [← sum_sfiniteSeq ν, ← sum_sfiniteSeq ν', sum_add_sum, ← sum_sfiniteSeq μ, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, left_distrib]

/--
theorem `add_prod` / 定理 `add_prod`

English:
theorem add_prod
  given: (μ' : Measure α) [SFinite μ']
  statement: (μ + μ').prod ν = μ.prod ν + μ'.prod ν
  proof: by
  simp_rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq μ', sum_add_sum, ← sum_sfiniteSeq ν, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, right_distrib]

@[simp]

中文:
定理 add_prod
  条件: (μ' : 测度 α) [SFinite μ']
  结论: (μ + μ').乘积 ν = μ.乘积 ν + μ'.乘积 ν
  证明: by
  simp_rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq μ', sum_add_sum, ← sum_sfiniteSeq ν, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, right_distrib]

@[simp]

Depends on / 依赖: add_apply, prod_eq, prod_prod, prod_sum, right_distrib, simp_rw, sum_add_sum, sum_sfiniteSeq
-/
theorem add_prod (μ' : Measure α) [SFinite μ'] : (μ + μ').prod ν = μ.prod ν + μ'.prod ν := by
  simp_rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq μ', sum_add_sum, ← sum_sfiniteSeq ν, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, right_distrib]

@[simp]
/--
theorem `zero_prod` / 定理 `zero_prod`

English:
theorem zero_prod
  given: (ν : Measure β)
  statement: (0 : Measure α).prod ν = 0
  proof: by
  rw [Measure.prod]
  exact bind_zero_left _

@[simp]

中文:
定理 zero_prod
  条件: (ν : 测度 β)
  结论: (0 : 测度 α).乘积 ν = 0
  证明: by
  rw [Measure.prod]
  exact bind_zero_left _

@[simp]

Depends on / 依赖: Measure, Measure.prod, bind_zero_left
-/
theorem zero_prod (ν : Measure β) : (0 : Measure α).prod ν = 0 := by
  rw [Measure.prod]
  exact bind_zero_left _

@[simp]
/--
theorem `prod_zero` / 定理 `prod_zero`

English:
theorem prod_zero
  given: (μ : Measure α)
  statement: μ.prod (0 : Measure β) = 0
  proof: by simp [Measure.prod]

中文:
定理 prod_zero
  条件: (μ : 测度 α)
  结论: μ.乘积 (0 : 测度 β) = 0
  证明: by simp [Measure.prod]

Depends on / 依赖: Measure, Measure.prod
-/
theorem prod_zero (μ : Measure α) : μ.prod (0 : Measure β) = 0 := by simp [Measure.prod]

/--
theorem `map_prod_map` / 定理 `map_prod_map`

English:
theorem map_prod_map
  statement: {δ} [MeasurableSpace δ] {f : α -> β} {g : γ -> δ} (μa : Measure α)
  proof: by
  simp_rw [← sum_sfiniteSeq μa, ← sum_sfiniteSeq μc, map_sum hf.aemeasurable,
    map_sum hg.aemeasurable, prod_sum, map_sum (hf.prodMap hg).aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  rw [map_apply (hf.prodMap hg) (hs.prod ht)]; rw [map_apply hf hs]; rw [map_apply hg ht

中文:
定理 map_prod_map
  结论: {δ} [可测空间 δ] {f : α -> β} {g : γ -> δ} (μa : 测度 α)
  证明: by
  simp_rw [← sum_sfiniteSeq μa, ← sum_sfiniteSeq μc, map_sum hf.aemeasurable,
    map_sum hg.aemeasurable, prod_sum, map_sum (hf.prodMap hg).aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  rw [map_apply (hf.prodMap hg) (hs.prod ht)]; rw [map_apply hf hs]; rw [map_apply hg ht

Depends on / 依赖: aemeasurable, hf.aemeasurable, hf.prodMap, hg.aemeasurable, hs.prod, map_apply, map_sum, prodMap, prod_eq, prod_prod, prod_sum, simp_rw, sum_sfiniteSeq
-/
theorem map_prod_map {δ} [MeasurableSpace δ] {f : α -> β} {g : γ -> δ} (μa : Measure α)
    (μc : Measure γ) [SFinite μa] [SFinite μc] (hf : Measurable f) (hg : Measurable g) :
    (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc) := by
  simp_rw [← sum_sfiniteSeq μa, ← sum_sfiniteSeq μc, map_sum hf.aemeasurable,
    map_sum hg.aemeasurable, prod_sum, map_sum (hf.prodMap hg).aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  rw [map_apply (hf.prodMap hg) (hs.prod ht)]; rw [map_apply hf hs]; rw [map_apply hg ht]
  exact prod_prod (f ⁻¹' s) (g ⁻¹' t)

-- `prod_smul_right` needs an instance to get `SFinite (c • ν)` from `SFinite ν`,
-- hence it is placed in the `WithDensity` file, where the instance is defined.
/--
lemma `prod_smul_left` / 引理 `prod_smul_left`

English:
lemma prod_smul_left
  statement: {μ : Measure α} {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: by
  ext s hs
  rw [prod_apply hs]; rw [Measure.smul_apply]; rw [prod_apply hs]
  simp

中文:
引理 prod_smul_left
  结论: {μ : 测度 α} {R : 类型} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: by
  ext s hs
  rw [prod_apply hs]; rw [Measure.smul_apply]; rw [prod_apply hs]
  simp

Depends on / 依赖: Measure, Measure.smul_apply, prod_apply, smul_apply
-/
lemma prod_smul_left {μ : Measure α} {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (c : R) : (c • μ).prod ν = c • (μ.prod ν) := by
  ext s hs
  rw [prod_apply hs]; rw [Measure.smul_apply]; rw [prod_apply hs]
  simp

end Measure

open Measure

namespace MeasurePreserving

variable {δ : Type*} [MeasurableSpace δ] {μa : Measure α} {μb : Measure β} {μc : Measure γ}
  {μd : Measure δ}

/--
theorem `skew_product` / 定理 `skew_product`

English:
theorem skew_product
  statement: [SFinite μa] [SFinite μc] {f : α -> β} (hf : MeasurePreserving f μa μb)
  proof: by
  have : Measurable fun p : α × γ => (f p.1, g p.1 p.2) := (hf.1.comp measurable_fst).prodMk hgm
  use this
  /- if `μa = 0`, then the lemma is trivial, otherwise we can use `hg`
    to deduce `SFinite μd`. -/
  rcases eq_zero_or_neZero μa with rfl | _
  · simp [← hf.map_eq]
  have sf : SFinite μ

中文:
定理 skew_product
  结论: [SFinite μa] [SFinite μc] {f : α -> β} (hf : 保测 f μa μb)
  证明: by
  have : Measurable fun p : α × γ => (f p.1, g p.1 p.2) := (hf.1.comp measurable_fst).prodMk hgm
  use this
  /- if `μa = 0`, then the lemma is trivial, otherwise we can use `hg`
    to deduce `SFinite μd`. -/
  rcases eq_zero_or_neZero μa with rfl | _
  · simp [← hf.map_eq]
  have sf : SFinite μ

Depends on / 依赖: Measurable, measurable_fst, prodMk
-/
theorem skew_product [SFinite μa] [SFinite μc] {f : α -> β} (hf : MeasurePreserving f μa μb)
    {g : α -> γ -> δ} (hgm : Measurable (uncurry g)) (hg : forallᵐ a ∂μa, map (g a) μc = μd) :
    MeasurePreserving (fun p : α × γ => (f p.1, g p.1 p.2)) (μa.prod μc) (μb.prod μd) := by
  have : Measurable fun p : α × γ => (f p.1, g p.1 p.2) := (hf.1.comp measurable_fst).prodMk hgm
  use this
  /- if `μa = 0`, then the lemma is trivial, otherwise we can use `hg`
    to deduce `SFinite μd`. -/
  rcases eq_zero_or_neZero μa with rfl | _
  · simp [← hf.map_eq]
  have sf : SFinite μd := by
    obtain ⟨a, ha⟩ : exists a, map (g a) μc = μd := hg.exists
    rw [← ha]
    infer_instance
  -- Thus we can use the integral formula for the product measure, and compute things explicitly
  ext s hs
  rw [map_apply this hs]; rw [Measure.prod_apply (this hs)]; rw [Measure.prod_apply hs]; rw [← hf.lintegral_comp (measurable_measure_prodMk_left hs)]
  apply lintegral_congr_ae
  filter_upwards [hg] with a ha
  rw [← ha]; rw [map_apply hgm.of_uncurry_left (measurable_prodMk_left hs)]; rw [preimage_preimage]; rw [preimage_preimage]

/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  statement: [SFinite μa] [SFinite μc] {f : α -> β} {g : γ -> δ}
  proof: have : Measurable (uncurry fun _ : α => g) := hg.1.comp measurable_snd
hf.skew_product this ae_of_all _ fun _ => hg.map_eq

中文:
定理 乘积
  结论: [SFinite μa] [SFinite μc] {f : α -> β} {g : γ -> δ}
  证明: have : Measurable (uncurry fun _ : α => g) := hg.1.comp measurable_snd
hf.skew_product this ae_of_all _ fun _ => hg.map_eq
-/
protected theorem prod [SFinite μa] [SFinite μc] {f : α -> β} {g : γ -> δ}
    (hf : MeasurePreserving f μa μb) (hg : MeasurePreserving g μc μd) :
    MeasurePreserving (Prod.map f g) (μa.prod μc) (μb.prod μd) :=
  have : Measurable (uncurry fun _ : α => g) := hg.1.comp measurable_snd
hf.skew_product this ae_of_all _ fun _ => hg.map_eq

end MeasurePreserving

namespace QuasiMeasurePreserving

/--
theorem `prod_of_right` / 定理 `prod_of_right`

English:
theorem prod_of_right
  statement: {f : α × β -> γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ}
  proof: by
  refine ⟨hf, ?_⟩
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  rw [map_apply hf hs]; rw [Measure.prod_apply (hf hs)]; simp_rw [preimage_preimage]
  rw [lintegral_congr_ae (h2f.mono fun x hx => hx.preimage_null h2s)]; rw [lintegral_zero]

中文:
定理 prod_of_right
  结论: {f : α × β -> γ} {μ : 测度 α} {ν : 测度 β} {τ : 测度 γ}
  证明: by
  refine ⟨hf, ?_⟩
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  rw [map_apply hf hs]; rw [Measure.prod_apply (hf hs)]; simp_rw [preimage_preimage]
  rw [lintegral_congr_ae (h2f.mono fun x hx => hx.preimage_null h2s)]; rw [lintegral_zero]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, Measure, Measure.prod_apply, h2f.mono, hx.preimage_null, lintegral_congr_ae, lintegral_zero, map_apply, preimage_null, preimage_preimage, prod_apply, simp_rw
-/
theorem prod_of_right {f : α × β -> γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    (hf : Measurable f) [SFinite ν]
    (h2f : forallᵐ x ∂μ, QuasiMeasurePreserving (fun y => f (x, y)) ν τ) :
    QuasiMeasurePreserving f (μ.prod ν) τ := by
  refine ⟨hf, ?_⟩
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  rw [map_apply hf hs]; rw [Measure.prod_apply (hf hs)]; simp_rw [preimage_preimage]
  rw [lintegral_congr_ae (h2f.mono fun x hx => hx.preimage_null h2s)]; rw [lintegral_zero]

/--
theorem `prod_of_left` / 定理 `prod_of_left`

English:
theorem prod_of_left
  statement: {α β γ} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  proof: by
  rw [← prod_swap]
  convert!
    (QuasiMeasurePreserving.prod_of_right (hf.comp measurable_swap) h2f).comp
      ((measurable_swap.measurePreserving (ν.prod μ)).symm
          MeasurableEquiv.prodComm).quasiMeasurePreserving

@[fun_prop]

中文:
定理 prod_of_left
  结论: {α β γ} [可测空间 α] [可测空间 β] [可测空间 γ]
  证明: by
  rw [← prod_swap]
  convert!
    (QuasiMeasurePreserving.prod_of_right (hf.comp measurable_swap) h2f).comp
      ((measurable_swap.measurePreserving (ν.prod μ)).symm
          MeasurableEquiv.prodComm).quasiMeasurePreserving

@[fun_prop]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.prodComm, QuasiMeasurePreserving, QuasiMeasurePreserving.prod_of_right, convert, hf.comp, measurable_swap, measurable_swap.measurePreserving, measurePreserving, prodComm, prod_of_right, prod_swap, quasiMeasurePreserving
-/
theorem prod_of_left {α β γ} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α × β -> γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ} (hf : Measurable f)
    [SFinite μ] [SFinite ν]
    (h2f : forallᵐ y ∂ν, QuasiMeasurePreserving (fun x => f (x, y)) μ τ) :
    QuasiMeasurePreserving f (μ.prod ν) τ := by
  rw [← prod_swap]
  convert!
    (QuasiMeasurePreserving.prod_of_right (hf.comp measurable_swap) h2f).comp
      ((measurable_swap.measurePreserving (ν.prod μ)).symm
          MeasurableEquiv.prodComm).quasiMeasurePreserving

@[fun_prop]
/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  given: {f : α -> β × γ} (hf : QuasiMeasurePreserving f μ (ν.prod τ))
  proof: (quasiMeasurePreserving_fst (μ := ν) (ν := τ)).comp hf

@[fun_prop]

中文:
定理 fst
  条件: {f : α -> β × γ} (hf : 拟保测 f μ (ν.乘积 τ))
  证明: (quasiMeasurePreserving_fst (μ := ν) (ν := τ)).comp hf

@[fun_prop]
-/
protected theorem fst {f : α -> β × γ} (hf : QuasiMeasurePreserving f μ (ν.prod τ)) :
    QuasiMeasurePreserving (fun x => (f x).1) μ ν :=
  (quasiMeasurePreserving_fst (μ := ν) (ν := τ)).comp hf

@[fun_prop]
/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  given: {f : α -> β × γ} (hf : QuasiMeasurePreserving f μ (ν.prod τ))
  proof: (quasiMeasurePreserving_snd (μ := ν) (ν := τ)).comp hf

@[fun_prop]

中文:
定理 snd
  条件: {f : α -> β × γ} (hf : 拟保测 f μ (ν.乘积 τ))
  证明: (quasiMeasurePreserving_snd (μ := ν) (ν := τ)).comp hf

@[fun_prop]
-/
protected theorem snd {f : α -> β × γ} (hf : QuasiMeasurePreserving f μ (ν.prod τ)) :
    QuasiMeasurePreserving (fun x => (f x).2) μ τ :=
  (quasiMeasurePreserving_snd (μ := ν) (ν := τ)).comp hf

@[fun_prop]
/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {ω : Type*} {mω : MeasurableSpace ω} {υ : Measure ω}
  proof: by
  refine ⟨by fun_prop, ?_⟩
  rw [← map_prod_map _ _ (by fun_prop) (by fun_prop)]
  exact hf.absolutelyContinuous.prod hg.absolutelyContinuous

中文:
定理 prodMap
  结论: {ω : 类型} {mω : 可测空间 ω} {υ : 测度 ω}
  证明: by
  refine ⟨by fun_prop, ?_⟩
  rw [← map_prod_map _ _ (by fun_prop) (by fun_prop)]
  exact hf.absolutelyContinuous.prod hg.absolutelyContinuous
-/
protected theorem prodMap {ω : Type*} {mω : MeasurableSpace ω} {υ : Measure ω}
    [SFinite μ] [SFinite τ] [SFinite υ] {f : α -> β} {g : γ -> ω}
    (hf : QuasiMeasurePreserving f μ ν) (hg : QuasiMeasurePreserving g τ υ) :
    QuasiMeasurePreserving (Prod.map f g) (μ.prod τ) (ν.prod υ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← map_prod_map _ _ (by fun_prop) (by fun_prop)]
  exact hf.absolutelyContinuous.prod hg.absolutelyContinuous

end QuasiMeasurePreserving

end MeasureTheory

open MeasureTheory.Measure

section

/--
theorem `AEMeasurable.prod_swap` / 定理 `AEMeasurable.prod_swap`

English:
theorem AEMeasurable.prod_swap
  statement: [SFinite μ] [SFinite ν] {f : β × α -> γ}
  proof: by
  rw [← Measure.prod_swap] at hf
  exact hf.comp_measurable measurable_swap

中文:
定理 几乎处处可测.prod_swap
  结论: [SFinite μ] [SFinite ν] {f : β × α -> γ}
  证明: by
  rw [← Measure.prod_swap] at hf
  exact hf.comp_measurable measurable_swap

Depends on / 依赖: Measure, Measure.prod_swap, comp_measurable, hf.comp_measurable, measurable_swap, prod_swap
-/
theorem AEMeasurable.prod_swap [SFinite μ] [SFinite ν] {f : β × α -> γ}
    (hf : AEMeasurable f (ν.prod μ)) : AEMeasurable (fun z : α × β => f z.swap) (μ.prod ν) := by
  rw [← Measure.prod_swap] at hf
  exact hf.comp_measurable measurable_swap

/--
theorem `MeasureTheory.NullMeasurable.comp_fst` / 定理 `MeasureTheory.NullMeasurable.comp_fst`

English:
theorem MeasureTheory.NullMeasurable.comp_fst
  given: {f : α -> γ} (hf : NullMeasurable f μ)
  proof: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

中文:
定理 测度论.NullMeasurable.comp_fst
  条件: {f : α -> γ} (hf : NullMeasurable f μ)
  证明: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

Depends on / 依赖: comp_quasiMeasurePreserving, hf.comp_quasiMeasurePreserving, quasiMeasurePreserving_fst
-/
theorem MeasureTheory.NullMeasurable.comp_fst {f : α -> γ} (hf : NullMeasurable f μ) :
    NullMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

/--
theorem `AEMeasurable.comp_fst` / 定理 `AEMeasurable.comp_fst`

English:
theorem AEMeasurable.comp_fst
  given: {f : α -> γ} (hf : AEMeasurable f μ)
  proof: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

中文:
定理 几乎处处可测.comp_fst
  条件: {f : α -> γ} (hf : 几乎处处可测 f μ)
  证明: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

Depends on / 依赖: comp_quasiMeasurePreserving, hf.comp_quasiMeasurePreserving, quasiMeasurePreserving_fst
-/
theorem AEMeasurable.comp_fst {f : α -> γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

/--
theorem `MeasureTheory.NullMeasurable.comp_snd` / 定理 `MeasureTheory.NullMeasurable.comp_snd`

English:
theorem MeasureTheory.NullMeasurable.comp_snd
  given: {f : β -> γ} (hf : NullMeasurable f ν)
  proof: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

中文:
定理 测度论.NullMeasurable.comp_snd
  条件: {f : β -> γ} (hf : NullMeasurable f ν)
  证明: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

Depends on / 依赖: comp_quasiMeasurePreserving, hf.comp_quasiMeasurePreserving, quasiMeasurePreserving_snd
-/
theorem MeasureTheory.NullMeasurable.comp_snd {f : β -> γ} (hf : NullMeasurable f ν) :
    NullMeasurable (fun z : α × β => f z.2) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

/--
theorem `AEMeasurable.comp_snd` / 定理 `AEMeasurable.comp_snd`

English:
theorem AEMeasurable.comp_snd
  given: {f : β -> γ} (hf : AEMeasurable f ν)
  proof: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

中文:
定理 几乎处处可测.comp_snd
  条件: {f : β -> γ} (hf : 几乎处处可测 f ν)
  证明: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

Depends on / 依赖: comp_quasiMeasurePreserving, hf.comp_quasiMeasurePreserving, quasiMeasurePreserving_snd
-/
theorem AEMeasurable.comp_snd {f : β -> γ} (hf : AEMeasurable f ν) :
    AEMeasurable (fun z : α × β => f z.2) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

/--
theorem `AEMeasurable.lintegral_prod_right'` / 定理 `AEMeasurable.lintegral_prod_right'`

English:
theorem AEMeasurable.lintegral_prod_right'
  statement: [SFinite ν] {f : α × β -> Real>=0∞}
  proof: by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun x => ∫⁻ y, g (x, y) ∂ν, by fun_prop, ?_⟩
  exact (ae_ae_of_ae_prod hfg).mono fun x hfg' => lintegral_congr_ae hfg'

@[fun_prop]

中文:
定理 几乎处处可测.lintegral_prod_right'
  结论: [SFinite ν] {f : α × β -> 实数>=0∞}
  证明: by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun x => ∫⁻ y, g (x, y) ∂ν, by fun_prop, ?_⟩
  exact (ae_ae_of_ae_prod hfg).mono fun x hfg' => lintegral_congr_ae hfg'

@[fun_prop]

Depends on / 依赖: ae_ae_of_ae_prod, fun_prop, lintegral_congr_ae
-/
theorem AEMeasurable.lintegral_prod_right' [SFinite ν] {f : α × β -> Real>=0∞}
    (hf : AEMeasurable f (μ.prod ν)) : AEMeasurable (fun x => ∫⁻ y, f (x, y) ∂ν) μ := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun x => ∫⁻ y, g (x, y) ∂ν, by fun_prop, ?_⟩
  exact (ae_ae_of_ae_prod hfg).mono fun x hfg' => lintegral_congr_ae hfg'

@[fun_prop]
/--
theorem `AEMeasurable.lintegral_prod_right` / 定理 `AEMeasurable.lintegral_prod_right`

English:
theorem AEMeasurable.lintegral_prod_right
  statement: [SFinite ν] {f : α -> β -> Real>=0∞}
  proof: hf.lintegral_prod_right'

中文:
定理 几乎处处可测.lintegral_prod_right
  结论: [SFinite ν] {f : α -> β -> 实数>=0∞}
  证明: hf.lintegral_prod_right'

Depends on / 依赖: hf.lintegral_prod_right, lintegral_prod_right
-/
theorem AEMeasurable.lintegral_prod_right [SFinite ν] {f : α -> β -> Real>=0∞}
    (hf : AEMeasurable f.uncurry (μ.prod ν)) : AEMeasurable (fun x => ∫⁻ y, f x y ∂ν) μ :=
  hf.lintegral_prod_right'

/--
theorem `AEMeasurable.lintegral_prod_left'` / 定理 `AEMeasurable.lintegral_prod_left'`

English:
theorem AEMeasurable.lintegral_prod_left'
  statement: [SFinite ν] [SFinite μ] {f : α × β -> Real>=0∞}
  proof: hf.prod_swap.lintegral_prod_right'

@[fun_prop]

中文:
定理 几乎处处可测.lintegral_prod_left'
  结论: [SFinite ν] [SFinite μ] {f : α × β -> 实数>=0∞}
  证明: hf.prod_swap.lintegral_prod_right'

@[fun_prop]

Depends on / 依赖: hf.prod_swap.lintegral_prod_right, lintegral_prod_right, prod_swap
-/
theorem AEMeasurable.lintegral_prod_left' [SFinite ν] [SFinite μ] {f : α × β -> Real>=0∞}
    (hf : AEMeasurable f (μ.prod ν)) : AEMeasurable (fun y => ∫⁻ x, f (x, y) ∂μ) ν :=
  hf.prod_swap.lintegral_prod_right'

@[fun_prop]
/--
theorem `AEMeasurable.lintegral_prod_left` / 定理 `AEMeasurable.lintegral_prod_left`

English:
theorem AEMeasurable.lintegral_prod_left
  statement: [SFinite ν] [SFinite μ] {f : α -> β -> Real>=0∞}
  proof: hf.lintegral_prod_left'

中文:
定理 几乎处处可测.lintegral_prod_left
  结论: [SFinite ν] [SFinite μ] {f : α -> β -> 实数>=0∞}
  证明: hf.lintegral_prod_left'

Depends on / 依赖: hf.lintegral_prod_left, lintegral_prod_left
-/
theorem AEMeasurable.lintegral_prod_left [SFinite ν] [SFinite μ] {f : α -> β -> Real>=0∞}
    (hf : AEMeasurable f.uncurry (μ.prod ν)) : AEMeasurable (fun y => ∫⁻ x, f x y ∂μ) ν :=
  hf.lintegral_prod_left'

end

namespace MeasureTheory

/-! ### The Lebesgue integral on a product -/

variable [SFinite ν]

/--
theorem `lintegral_prod_swap` / 定理 `lintegral_prod_swap`

English:
theorem lintegral_prod_swap
  given: [SFinite μ] (f : α × β -> Real>=0∞)
  proof: measurePreserving_swap.lintegral_comp_emb MeasurableEquiv.prodComm.measurableEmbedding f

中文:
定理 lintegral_prod_swap
  条件: [SFinite μ] (f : α × β -> 实数>=0∞)
  证明: measurePreserving_swap.lintegral_comp_emb MeasurableEquiv.prodComm.measurableEmbedding f

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.prodComm.measurableEmbedding, lintegral_comp_emb, measurableEmbedding, measurePreserving_swap, measurePreserving_swap.lintegral_comp_emb, prodComm
-/
theorem lintegral_prod_swap [SFinite μ] (f : α × β -> Real>=0∞) :
    ∫⁻ z, f z.swap ∂ν.prod μ = ∫⁻ z, f z ∂μ.prod ν :=
  measurePreserving_swap.lintegral_comp_emb MeasurableEquiv.prodComm.measurableEmbedding f

/--
theorem `lintegral_prod` / 定理 `lintegral_prod`

English:
theorem lintegral_prod
  given: (f : α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν))
  proof: by
  rw [Measure.prod] at *
  rw [lintegral_bind Measurable.map_prodMk_left.aemeasurable hf]
  apply lintegral_congr_ae
  filter_upwards [Measurable.map_prodMk_left.aemeasurable.ae_of_bind hf] with a ha
  exact lintegral_map' ha (by fun_prop)

omit [SFinite ν] in

中文:
定理 lintegral_prod
  条件: (f : α × β -> 实数>=0∞) (hf : 几乎处处可测 f (μ.乘积 ν))
  证明: by
  rw [Measure.prod] at *
  rw [lintegral_bind Measurable.map_prodMk_left.aemeasurable hf]
  apply lintegral_congr_ae
  filter_upwards [Measurable.map_prodMk_left.aemeasurable.ae_of_bind hf] with a ha
  exact lintegral_map' ha (by fun_prop)

omit [SFinite ν] in

Depends on / 依赖: Measurable, Measurable.map_prodMk_left.aemeasurable, Measurable.map_prodMk_left.aemeasurable.ae_of_bind, Measure, Measure.prod, ae_of_bind, aemeasurable, filter_upwards, fun_prop, lintegral_bind, lintegral_congr_ae, lintegral_map, map_prodMk_left
-/
theorem lintegral_prod (f : α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [Measure.prod] at *
  rw [lintegral_bind Measurable.map_prodMk_left.aemeasurable hf]
  apply lintegral_congr_ae
  filter_upwards [Measurable.map_prodMk_left.aemeasurable.ae_of_bind hf] with a ha
  exact lintegral_map' ha (by fun_prop)

omit [SFinite ν] in
/--
theorem `lintegral_prod_le` / 定理 `lintegral_prod_le`

English:
theorem lintegral_prod_le
  given: (f : α × β -> Real>=0∞)
  proof: by
  rw [Measure.prod]
exact (lintegral_bind_le _ _ _).trans lintegral_mono fun a => lintegral_map_le _ _

中文:
定理 lintegral_prod_le
  条件: (f : α × β -> 实数>=0∞)
  证明: by
  rw [Measure.prod]
exact (lintegral_bind_le _ _ _).trans lintegral_mono fun a => lintegral_map_le _ _

Depends on / 依赖: Measure, Measure.prod, lintegral_bind_le, lintegral_map_le, lintegral_mono
-/
theorem lintegral_prod_le (f : α × β -> Real>=0∞) :
    ∫⁻ z, f z ∂μ.prod ν <= ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [Measure.prod]
exact (lintegral_bind_le _ _ _).trans lintegral_mono fun a => lintegral_map_le _ _

/--
theorem `setLIntegral_prod` / 定理 `setLIntegral_prod`

English:
theorem setLIntegral_prod
  statement: [SFinite μ] {s : Set α} {t : Set β} (f : α × β -> Real>=0∞)
  proof: by
  rw [← Measure.prod_restrict]; rw [lintegral_prod _ (by rwa [Measure.prod_restrict])]

中文:
定理 setL整数egral_prod
  结论: [SFinite μ] {s : 集合 α} {t : 集合 β} (f : α × β -> 实数>=0∞)
  证明: by
  rw [← Measure.prod_restrict]; rw [lintegral_prod _ (by rwa [Measure.prod_restrict])]

Depends on / 依赖: Measure, Measure.prod_restrict, lintegral_prod, prod_restrict
-/
theorem setLIntegral_prod [SFinite μ] {s : Set α} {t : Set β} (f : α × β -> Real>=0∞)
    (hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))) :
    ∫⁻ z in s ×ˢ t, f z ∂μ.prod ν = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂ν ∂μ := by
  rw [← Measure.prod_restrict]; rw [lintegral_prod _ (by rwa [Measure.prod_restrict])]

/--
theorem `lintegral_prod_symm` / 定理 `lintegral_prod_symm`

English:
theorem lintegral_prod_symm
  given: [SFinite μ] (f : α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν))
  proof: by
  simp_rw [← lintegral_prod_swap f]
  exact lintegral_prod _ hf.prod_swap

中文:
定理 lintegral_prod_symm
  条件: [SFinite μ] (f : α × β -> 实数>=0∞) (hf : 几乎处处可测 f (μ.乘积 ν))
  证明: by
  simp_rw [← lintegral_prod_swap f]
  exact lintegral_prod _ hf.prod_swap

Depends on / 依赖: hf.prod_swap, lintegral_prod, lintegral_prod_swap, prod_swap, simp_rw
-/
theorem lintegral_prod_symm [SFinite μ] (f : α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  simp_rw [← lintegral_prod_swap f]
  exact lintegral_prod _ hf.prod_swap

/--
theorem `lintegral_prod_symm'` / 定理 `lintegral_prod_symm'`

English:
theorem lintegral_prod_symm'
  given: [SFinite μ] (f : α × β -> Real>=0∞) (hf : Measurable f)
  proof: lintegral_prod_symm f hf.aemeasurable

中文:
定理 lintegral_prod_symm'
  条件: [SFinite μ] (f : α × β -> 实数>=0∞) (hf : 可测 f)
  证明: lintegral_prod_symm f hf.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable, lintegral_prod_symm
-/
theorem lintegral_prod_symm' [SFinite μ] (f : α × β -> Real>=0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
  lintegral_prod_symm f hf.aemeasurable

/--
theorem `setLIntegral_prod_symm` / 定理 `setLIntegral_prod_symm`

English:
theorem setLIntegral_prod_symm
  statement: [SFinite μ] {s : Set α} {t : Set β} (f : α × β -> Real>=0∞)
  proof: by
  rw [← Measure.prod_restrict]; rw [← lintegral_prod_swap]; rw [Measure.prod_restrict]; rw [setLIntegral_prod]
  · rfl
  · refine AEMeasurable.comp_measurable ?_ measurable_swap
    convert! hf
    rw [← Measure.prod_restrict]; rw [Measure.prod_swap]; rw [Measure.prod_restrict]

中文:
定理 setL整数egral_prod_symm
  结论: [SFinite μ] {s : 集合 α} {t : 集合 β} (f : α × β -> 实数>=0∞)
  证明: by
  rw [← Measure.prod_restrict]; rw [← lintegral_prod_swap]; rw [Measure.prod_restrict]; rw [setLIntegral_prod]
  · rfl
  · refine AEMeasurable.comp_measurable ?_ measurable_swap
    convert! hf
    rw [← Measure.prod_restrict]; rw [Measure.prod_swap]; rw [Measure.prod_restrict]

Depends on / 依赖: AEMeasurable, AEMeasurable.comp_measurable, Measure, Measure.prod_restrict, Measure.prod_swap, comp_measurable, convert, lintegral_prod_swap, measurable_swap, prod_restrict, prod_swap, setLIntegral_prod
-/
theorem setLIntegral_prod_symm [SFinite μ] {s : Set α} {t : Set β} (f : α × β -> Real>=0∞)
    (hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))) :
    ∫⁻ z in s ×ˢ t, f z ∂μ.prod ν = ∫⁻ y in t, ∫⁻ x in s, f (x, y) ∂μ ∂ν := by
  rw [← Measure.prod_restrict]; rw [← lintegral_prod_swap]; rw [Measure.prod_restrict]; rw [setLIntegral_prod]
  · rfl
  · refine AEMeasurable.comp_measurable ?_ measurable_swap
    convert! hf
    rw [← Measure.prod_restrict]; rw [Measure.prod_swap]; rw [Measure.prod_restrict]

/--
theorem `lintegral_lintegral` / 定理 `lintegral_lintegral`

English:
theorem lintegral_lintegral
  given: ⦃f
  statement: α -> β -> Real>=0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
  proof: (lintegral_prod _ hf).symm

中文:
定理 lintegral_lintegral
  条件: ⦃f
  结论: α -> β -> 实数>=0∞⦄ (hf : 几乎处处可测 (uncurry f) (μ.乘积 ν)) :
  证明: (lintegral_prod _ hf).symm

Depends on / 依赖: lintegral_prod
-/
theorem lintegral_lintegral ⦃f : α -> β -> Real>=0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.1 z.2 ∂μ.prod ν :=
  (lintegral_prod _ hf).symm

/--
theorem `lintegral_lintegral_symm` / 定理 `lintegral_lintegral_symm`

English:
theorem lintegral_lintegral_symm
  given: [SFinite μ] ⦃f
  statement: α -> β -> Real>=0∞⦄
  proof: (lintegral_prod_symm _ hf.prod_swap).symm

中文:
定理 lintegral_lintegral_symm
  条件: [SFinite μ] ⦃f
  结论: α -> β -> 实数>=0∞⦄
  证明: (lintegral_prod_symm _ hf.prod_swap).symm

Depends on / 依赖: hf.prod_swap, lintegral_prod_symm, prod_swap
-/
theorem lintegral_lintegral_symm [SFinite μ] ⦃f : α -> β -> Real>=0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.2 z.1 ∂ν.prod μ :=
  (lintegral_prod_symm _ hf.prod_swap).symm

/--
theorem `lintegral_lintegral_swap` / 定理 `lintegral_lintegral_swap`

English:
theorem lintegral_lintegral_swap
  given: [SFinite μ] ⦃f
  statement: α -> β -> Real>=0∞⦄
  proof: (lintegral_lintegral hf).trans (lintegral_prod_symm _ hf)

中文:
定理 lintegral_lintegral_swap
  条件: [SFinite μ] ⦃f
  结论: α -> β -> 实数>=0∞⦄
  证明: (lintegral_lintegral hf).trans (lintegral_prod_symm _ hf)

Depends on / 依赖: lintegral_lintegral, lintegral_prod_symm
-/
theorem lintegral_lintegral_swap [SFinite μ] ⦃f : α -> β -> Real>=0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν :=
  (lintegral_lintegral hf).trans (lintegral_prod_symm _ hf)

/--
theorem `lintegral_prod_mul` / 定理 `lintegral_prod_mul`

English:
theorem lintegral_prod_mul
  statement: {f : α -> Real>=0∞} {g : β -> Real>=0∞} (hf : AEMeasurable f μ)
  proof: by
  rw [lintegral_prod _ (by fun_prop)]
  simp [lintegral_lintegral_mul hf hg]

中文:
定理 lintegral_prod_mul
  结论: {f : α -> 实数>=0∞} {g : β -> 实数>=0∞} (hf : 几乎处处可测 f μ)
  证明: by
  rw [lintegral_prod _ (by fun_prop)]
  simp [lintegral_lintegral_mul hf hg]

Depends on / 依赖: fun_prop, lintegral_lintegral_mul, lintegral_prod
-/
theorem lintegral_prod_mul {f : α -> Real>=0∞} {g : β -> Real>=0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g ν) : ∫⁻ z, f z.1 * g z.2 ∂μ.prod ν = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  rw [lintegral_prod _ (by fun_prop)]
  simp [lintegral_lintegral_mul hf hg]

/-! ### Marginals of a measure defined on a product -/


namespace Measure

variable {ρ : Measure (α × β)}

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: (ρ : Measure (α × β))
  body: ρ.map Prod.fst

中文:
定义 fst
  签名: (ρ : 测度 (α × β))
  定义体: ρ.map Prod.fst

Depends on / 依赖: Prod.fst
-/
noncomputable def fst (ρ : Measure (α × β)) : Measure α :=
  ρ.map Prod.fst

/--
theorem `fst_apply` / 定理 `fst_apply`

English:
theorem fst_apply
  given: {s : Set α} (hs : MeasurableSet s)
  statement: ρ.fst s = ρ (Prod.fst ⁻¹' s)
  proof: by
  rw [fst]; rw [Measure.map_apply measurable_fst hs]

中文:
定理 fst_apply
  条件: {s : 集合 α} (hs : 可测集 s)
  结论: ρ.fst s = ρ (积类型.fst ⁻¹' s)
  证明: by
  rw [fst]; rw [Measure.map_apply measurable_fst hs]

Depends on / 依赖: Measure, Measure.map_apply, map_apply, measurable_fst
-/
theorem fst_apply {s : Set α} (hs : MeasurableSet s) : ρ.fst s = ρ (Prod.fst ⁻¹' s) := by
  rw [fst]; rw [Measure.map_apply measurable_fst hs]

/--
theorem `fst_univ` / 定理 `fst_univ`

English:
theorem fst_univ
  statement: ρ.fst univ = ρ univ
  proof: by rw [fst_apply MeasurableSet.univ, preimage_univ]

中文:
定理 fst_univ
  结论: ρ.fst univ = ρ univ
  证明: by rw [fst_apply MeasurableSet.univ, preimage_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, fst_apply, preimage_univ
-/
theorem fst_univ : ρ.fst univ = ρ univ := by rw [fst_apply MeasurableSet.univ, preimage_univ]

/--
theorem `fst_zero` / 定理 `fst_zero`

English:
theorem fst_zero
  statement: fst (0 : Measure (α × β)) = 0
  proof: by simp [fst]

中文:
定理 fst_zero
  结论: fst (0 : 测度 (α × β)) = 0
  证明: by simp [fst]
-/
@[simp] theorem fst_zero : fst (0 : Measure (α × β)) = 0 := by simp [fst]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SFinite
  signature: ρ] : SFinite ρ.fst
  body: by
  rw [fst]
  infer_instance

中文:
实例 [SFinite
  签名: ρ] : SFinite ρ.fst
  定义体: by
  rw [fst]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [SFinite ρ] : SFinite ρ.fst := by
  rw [fst]
  infer_instance

/--
Instance `fst.instIsFiniteMeasure` / 实例 `fst.instIsFiniteMeasure`

English:
instance fst.instIsFiniteMeasure
  signature: [IsFiniteMeasure ρ]
  body: by
  rw [fst]
  infer_instance

中文:
实例 fst.instIsFiniteMeasure
  签名: [是有限测度 ρ]
  定义体: by
  rw [fst]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance fst.instIsFiniteMeasure [IsFiniteMeasure ρ] : IsFiniteMeasure ρ.fst := by
  rw [fst]
  infer_instance

/--
Instance `fst.instIsProbabilityMeasure` / 实例 `fst.instIsProbabilityMeasure`

English:
instance fst.instIsProbabilityMeasure
  signature: [IsProbabilityMeasure ρ]
  body: by
    rw [fst_univ]
    exact measure_univ

中文:
实例 fst.instIsProbabilityMeasure
  签名: [是概率测度 ρ]
  定义体: by
    rw [fst_univ]
    exact measure_univ

Depends on / 依赖: fst_univ, measure_univ
-/
instance fst.instIsProbabilityMeasure [IsProbabilityMeasure ρ] : IsProbabilityMeasure ρ.fst where
  measure_univ := by
    rw [fst_univ]
    exact measure_univ

/--
Instance `fst.instIsZeroOrProbabilityMeasure` / 实例 `fst.instIsZeroOrProbabilityMeasure`

English:
instance fst.instIsZeroOrProbabilityMeasure
  signature: [IsZeroOrProbabilityMeasure ρ]
  body: by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, fst_zero]
    infer_instance
  · infer_instance

@[simp]

中文:
实例 fst.instIsZeroOrProbabilityMeasure
  签名: [是ZeroOrProbabilityMeasure ρ]
  定义体: by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, fst_zero]
    infer_instance
  · infer_instance

@[simp]

Depends on / 依赖: eq_zero_or_isProbabilityMeasure, fst_zero, infer_instance
-/
instance fst.instIsZeroOrProbabilityMeasure [IsZeroOrProbabilityMeasure ρ] :
    IsZeroOrProbabilityMeasure ρ.fst := by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, fst_zero]
    infer_instance
  · infer_instance

@[simp]
/--
lemma `fst_prod` / 引理 `fst_prod`

English:
lemma fst_prod
  given: [IsProbabilityMeasure ν]
  statement: (μ.prod ν).fst = μ
  proof: by
  ext1 s hs
  rw [fst_apply hs]; rw [← prod_univ]; rw [prod_prod]; rw [measure_univ]; rw [mul_one]

中文:
引理 fst_prod
  条件: [是概率测度 ν]
  结论: (μ.乘积 ν).fst = μ
  证明: by
  ext1 s hs
  rw [fst_apply hs]; rw [← prod_univ]; rw [prod_prod]; rw [measure_univ]; rw [mul_one]

Depends on / 依赖: fst_apply, measure_univ, mul_one, prod_prod, prod_univ
-/
lemma fst_prod [IsProbabilityMeasure ν] : (μ.prod ν).fst = μ := by
  ext1 s hs
  rw [fst_apply hs]; rw [← prod_univ]; rw [prod_prod]; rw [measure_univ]; rw [mul_one]

/--
theorem `fst_map_prodMk₀` / 定理 `fst_map_prodMk₀`

English:
theorem fst_map_prodMk₀
  statement: {X : α -> β} {Y : α -> γ} {μ : Measure α}
  proof: by
  by_cases hX : AEMeasurable X μ
  · ext1 s hs
    rw [Measure.fst_apply hs]; rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) (measurable_fst hs)]; rw [Measure.map_apply_of_aemeasurable hX hs]; rw [← prod_univ]; rw [mk_preimage_prod]; rw [preimage_univ]; rw [inter_univ]
  · have : ¬AEMeasura

中文:
定理 fst_map_prodMk₀
  结论: {X : α -> β} {Y : α -> γ} {μ : 测度 α}
  证明: by
  by_cases hX : AEMeasurable X μ
  · ext1 s hs
    rw [Measure.fst_apply hs]; rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) (measurable_fst hs)]; rw [Measure.map_apply_of_aemeasurable hX hs]; rw [← prod_univ]; rw [mk_preimage_prod]; rw [preimage_univ]; rw [inter_univ]
  · have : ¬AEMeasura

Depends on / 依赖: AEMeasurable, Measure, Measure.fst_apply, Measure.map_apply_of_aemeasurable, comp_aemeasurable, contrapose, fst_apply, hX.prodMk, inter_univ, map_apply_of_aemeasurable, map_of_not_aemeasurable, measurable_fst, measurable_fst.comp_aemeasurable, mk_preimage_prod, preimage_univ, prodMk, prod_univ
-/
theorem fst_map_prodMk₀ {X : α -> β} {Y : α -> γ} {μ : Measure α}
    (hY : AEMeasurable Y μ) : (μ.map fun a => (X a, Y a)).fst = μ.map X := by
  by_cases hX : AEMeasurable X μ
  · ext1 s hs
    rw [Measure.fst_apply hs]; rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) (measurable_fst hs)]; rw [Measure.map_apply_of_aemeasurable hX hs]; rw [← prod_univ]; rw [mk_preimage_prod]; rw [preimage_univ]; rw [inter_univ]
  · have : ¬AEMeasurable (fun x => (X x, Y x)) μ := by
      contrapose hX
      exact measurable_fst.comp_aemeasurable hX
    simp [map_of_not_aemeasurable, hX, this]

/--
theorem `fst_map_prodMk` / 定理 `fst_map_prodMk`

English:
theorem fst_map_prodMk
  statement: {X : α -> β} {Y : α -> γ} {μ : Measure α}
  proof: fst_map_prodMk₀ hY.aemeasurable

@[simp]

中文:
定理 fst_map_prodMk
  结论: {X : α -> β} {Y : α -> γ} {μ : 测度 α}
  证明: fst_map_prodMk₀ hY.aemeasurable

@[simp]

Depends on / 依赖: aemeasurable, hY.aemeasurable
-/
theorem fst_map_prodMk {X : α -> β} {Y : α -> γ} {μ : Measure α}
    (hY : Measurable Y) : (μ.map fun a => (X a, Y a)).fst = μ.map X :=
  fst_map_prodMk₀ hY.aemeasurable

@[simp]
/--
lemma `fst_add` / 引理 `fst_add`

English:
lemma fst_add
  given: {μ ν : Measure (α × β)}
  statement: (μ + ν).fst = μ.fst + ν.fst
  proof: Measure.map_add _ _ measurable_fst

中文:
引理 fst_add
  条件: {μ ν : 测度 (α × β)}
  结论: (μ + ν).fst = μ.fst + ν.fst
  证明: Measure.map_add _ _ measurable_fst

Depends on / 依赖: Measure, Measure.map_add, map_add, measurable_fst
-/
lemma fst_add {μ ν : Measure (α × β)} : (μ + ν).fst = μ.fst + ν.fst :=
  Measure.map_add _ _ measurable_fst

/--
lemma `fst_sum` / 引理 `fst_sum`

English:
lemma fst_sum
  given: {ι : Type*} (μ : ι -> Measure (α × β))
  statement: (sum μ).fst = sum (fun n => (μ n).fst)
  proof: Measure.map_sum measurable_fst.aemeasurable

@[gcongr]

中文:
引理 fst_sum
  条件: {ι : 类型} (μ : ι -> 测度 (α × β))
  结论: (求和 μ).fst = 求和 (fun n => (μ n).fst)
  证明: Measure.map_sum measurable_fst.aemeasurable

@[gcongr]

Depends on / 依赖: Measure, Measure.map_sum, aemeasurable, map_sum, measurable_fst, measurable_fst.aemeasurable
-/
lemma fst_sum {ι : Type*} (μ : ι -> Measure (α × β)) : (sum μ).fst = sum (fun n => (μ n).fst) :=
  Measure.map_sum measurable_fst.aemeasurable

@[gcongr]
/--
theorem `fst_mono` / 定理 `fst_mono`

English:
theorem fst_mono
  given: {μ : Measure (α × β)} (h : ρ <= μ)
  statement: ρ.fst <= μ.fst
  proof: map_mono h measurable_fst

中文:
定理 fst_mono
  条件: {μ : 测度 (α × β)} (h : ρ <= μ)
  结论: ρ.fst <= μ.fst
  证明: map_mono h measurable_fst

Depends on / 依赖: map_mono, measurable_fst
-/
theorem fst_mono {μ : Measure (α × β)} (h : ρ <= μ) : ρ.fst <= μ.fst := map_mono h measurable_fst

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: (ρ : Measure (α × β))
  body: ρ.map Prod.snd

中文:
定义 snd
  签名: (ρ : 测度 (α × β))
  定义体: ρ.map Prod.snd

Depends on / 依赖: Prod.snd
-/
noncomputable def snd (ρ : Measure (α × β)) : Measure β :=
  ρ.map Prod.snd

/--
theorem `snd_apply` / 定理 `snd_apply`

English:
theorem snd_apply
  given: {s : Set β} (hs : MeasurableSet s)
  statement: ρ.snd s = ρ (Prod.snd ⁻¹' s)
  proof: by
  rw [snd]; rw [Measure.map_apply measurable_snd hs]

中文:
定理 snd_apply
  条件: {s : 集合 β} (hs : 可测集 s)
  结论: ρ.snd s = ρ (积类型.snd ⁻¹' s)
  证明: by
  rw [snd]; rw [Measure.map_apply measurable_snd hs]

Depends on / 依赖: Measure, Measure.map_apply, map_apply, measurable_snd
-/
theorem snd_apply {s : Set β} (hs : MeasurableSet s) : ρ.snd s = ρ (Prod.snd ⁻¹' s) := by
  rw [snd]; rw [Measure.map_apply measurable_snd hs]

/--
theorem `snd_univ` / 定理 `snd_univ`

English:
theorem snd_univ
  statement: ρ.snd univ = ρ univ
  proof: by rw [snd_apply MeasurableSet.univ, preimage_univ]

中文:
定理 snd_univ
  结论: ρ.snd univ = ρ univ
  证明: by rw [snd_apply MeasurableSet.univ, preimage_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, preimage_univ, snd_apply
-/
theorem snd_univ : ρ.snd univ = ρ univ := by rw [snd_apply MeasurableSet.univ, preimage_univ]

/--
theorem `snd_zero` / 定理 `snd_zero`

English:
theorem snd_zero
  statement: snd (0 : Measure (α × β)) = 0
  proof: by simp [snd]

中文:
定理 snd_zero
  结论: snd (0 : 测度 (α × β)) = 0
  证明: by simp [snd]
-/
@[simp] theorem snd_zero : snd (0 : Measure (α × β)) = 0 := by simp [snd]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SFinite
  signature: ρ] : SFinite ρ.snd
  body: by
  rw [snd]
  infer_instance

中文:
实例 [SFinite
  签名: ρ] : SFinite ρ.snd
  定义体: by
  rw [snd]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [SFinite ρ] : SFinite ρ.snd := by
  rw [snd]
  infer_instance

/--
Instance `snd.instIsFiniteMeasure` / 实例 `snd.instIsFiniteMeasure`

English:
instance snd.instIsFiniteMeasure
  signature: [IsFiniteMeasure ρ]
  body: by
  rw [snd]
  infer_instance

中文:
实例 snd.instIsFiniteMeasure
  签名: [是有限测度 ρ]
  定义体: by
  rw [snd]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance snd.instIsFiniteMeasure [IsFiniteMeasure ρ] : IsFiniteMeasure ρ.snd := by
  rw [snd]
  infer_instance

/--
Instance `snd.instIsProbabilityMeasure` / 实例 `snd.instIsProbabilityMeasure`

English:
instance snd.instIsProbabilityMeasure
  signature: [IsProbabilityMeasure ρ]
  body: by
    rw [snd_univ]
    exact measure_univ

中文:
实例 snd.instIsProbabilityMeasure
  签名: [是概率测度 ρ]
  定义体: by
    rw [snd_univ]
    exact measure_univ

Depends on / 依赖: measure_univ, snd_univ
-/
instance snd.instIsProbabilityMeasure [IsProbabilityMeasure ρ] : IsProbabilityMeasure ρ.snd where
  measure_univ := by
    rw [snd_univ]
    exact measure_univ

/--
Instance `snd.instIsZeroOrProbabilityMeasure` / 实例 `snd.instIsZeroOrProbabilityMeasure`

English:
instance snd.instIsZeroOrProbabilityMeasure
  signature: [IsZeroOrProbabilityMeasure ρ]
  body: by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, snd_zero]
    infer_instance
  · infer_instance

@[simp]

中文:
实例 snd.instIsZeroOrProbabilityMeasure
  签名: [是ZeroOrProbabilityMeasure ρ]
  定义体: by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, snd_zero]
    infer_instance
  · infer_instance

@[simp]

Depends on / 依赖: eq_zero_or_isProbabilityMeasure, infer_instance, snd_zero
-/
instance snd.instIsZeroOrProbabilityMeasure [IsZeroOrProbabilityMeasure ρ] :
    IsZeroOrProbabilityMeasure ρ.snd := by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, snd_zero]
    infer_instance
  · infer_instance

@[simp]
/--
lemma `snd_prod` / 引理 `snd_prod`

English:
lemma snd_prod
  given: [IsProbabilityMeasure μ]
  statement: (μ.prod ν).snd = ν
  proof: by
  ext1 s hs
  rw [snd_apply hs]; rw [← univ_prod]; rw [prod_prod]; rw [measure_univ]; rw [one_mul]

中文:
引理 snd_prod
  条件: [是概率测度 μ]
  结论: (μ.乘积 ν).snd = ν
  证明: by
  ext1 s hs
  rw [snd_apply hs]; rw [← univ_prod]; rw [prod_prod]; rw [measure_univ]; rw [one_mul]

Depends on / 依赖: measure_univ, one_mul, prod_prod, snd_apply, univ_prod
-/
lemma snd_prod [IsProbabilityMeasure μ] : (μ.prod ν).snd = ν := by
  ext1 s hs
  rw [snd_apply hs]; rw [← univ_prod]; rw [prod_prod]; rw [measure_univ]; rw [one_mul]

/--
theorem `snd_map_prodMk₀` / 定理 `snd_map_prodMk₀`

English:
theorem snd_map_prodMk₀
  given: {X : α -> β} {Y : α -> γ} {μ : Measure α} (hX : AEMeasurable X μ)
  proof: by
  by_cases hY : AEMeasurable Y μ
  · ext1 s hs
    rw [Measure.snd_apply hs]; rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) (measurable_snd hs)]; rw [Measure.map_apply_of_aemeasurable hY hs]; rw [← univ_prod]; rw [mk_preimage_prod]; rw [preimage_univ]; rw [univ_inter]
  · have : ¬AEMeasura

中文:
定理 snd_map_prodMk₀
  条件: {X : α -> β} {Y : α -> γ} {μ : 测度 α} (hX : 几乎处处可测 X μ)
  证明: by
  by_cases hY : AEMeasurable Y μ
  · ext1 s hs
    rw [Measure.snd_apply hs]; rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) (measurable_snd hs)]; rw [Measure.map_apply_of_aemeasurable hY hs]; rw [← univ_prod]; rw [mk_preimage_prod]; rw [preimage_univ]; rw [univ_inter]
  · have : ¬AEMeasura

Depends on / 依赖: AEMeasurable, Measure, Measure.map_apply_of_aemeasurable, Measure.snd_apply, comp_aemeasurable, contrapose, hX.prodMk, map_apply_of_aemeasurable, map_of_not_aemeasurable, measurable_snd, measurable_snd.comp_aemeasurable, mk_preimage_prod, preimage_univ, prodMk, snd_apply, univ_inter, univ_prod
-/
theorem snd_map_prodMk₀ {X : α -> β} {Y : α -> γ} {μ : Measure α} (hX : AEMeasurable X μ) :
    (μ.map fun a => (X a, Y a)).snd = μ.map Y := by
  by_cases hY : AEMeasurable Y μ
  · ext1 s hs
    rw [Measure.snd_apply hs]; rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) (measurable_snd hs)]; rw [Measure.map_apply_of_aemeasurable hY hs]; rw [← univ_prod]; rw [mk_preimage_prod]; rw [preimage_univ]; rw [univ_inter]
  · have : ¬AEMeasurable (fun x => (X x, Y x)) μ := by
      contrapose hY
      exact measurable_snd.comp_aemeasurable hY
    simp [map_of_not_aemeasurable, hY, this]

/--
theorem `snd_map_prodMk` / 定理 `snd_map_prodMk`

English:
theorem snd_map_prodMk
  given: {X : α -> β} {Y : α -> γ} {μ : Measure α} (hX : Measurable X)
  proof: snd_map_prodMk₀ hX.aemeasurable

@[simp]

中文:
定理 snd_map_prodMk
  条件: {X : α -> β} {Y : α -> γ} {μ : 测度 α} (hX : 可测 X)
  证明: snd_map_prodMk₀ hX.aemeasurable

@[simp]

Depends on / 依赖: aemeasurable, hX.aemeasurable
-/
theorem snd_map_prodMk {X : α -> β} {Y : α -> γ} {μ : Measure α} (hX : Measurable X) :
    (μ.map fun a => (X a, Y a)).snd = μ.map Y :=
  snd_map_prodMk₀ hX.aemeasurable

@[simp]
/--
lemma `snd_add` / 引理 `snd_add`

English:
lemma snd_add
  given: {μ ν : Measure (α × β)}
  statement: (μ + ν).snd = μ.snd + ν.snd
  proof: Measure.map_add _ _ measurable_snd

中文:
引理 snd_add
  条件: {μ ν : 测度 (α × β)}
  结论: (μ + ν).snd = μ.snd + ν.snd
  证明: Measure.map_add _ _ measurable_snd

Depends on / 依赖: Measure, Measure.map_add, map_add, measurable_snd
-/
lemma snd_add {μ ν : Measure (α × β)} : (μ + ν).snd = μ.snd + ν.snd :=
  Measure.map_add _ _ measurable_snd

/--
lemma `snd_sum` / 引理 `snd_sum`

English:
lemma snd_sum
  given: {ι : Type*} (μ : ι -> Measure (α × β))
  statement: (sum μ).snd = sum (fun n => (μ n).snd)
  proof: map_sum measurable_snd.aemeasurable

@[gcongr]

中文:
引理 snd_sum
  条件: {ι : 类型} (μ : ι -> 测度 (α × β))
  结论: (求和 μ).snd = 求和 (fun n => (μ n).snd)
  证明: map_sum measurable_snd.aemeasurable

@[gcongr]

Depends on / 依赖: aemeasurable, map_sum, measurable_snd, measurable_snd.aemeasurable
-/
lemma snd_sum {ι : Type*} (μ : ι -> Measure (α × β)) : (sum μ).snd = sum (fun n => (μ n).snd) :=
  map_sum measurable_snd.aemeasurable

@[gcongr]
/--
theorem `snd_mono` / 定理 `snd_mono`

English:
theorem snd_mono
  given: {μ : Measure (α × β)} (h : ρ <= μ)
  statement: ρ.snd <= μ.snd
  proof: map_mono h measurable_snd

中文:
定理 snd_mono
  条件: {μ : 测度 (α × β)} (h : ρ <= μ)
  结论: ρ.snd <= μ.snd
  证明: map_mono h measurable_snd

Depends on / 依赖: map_mono, measurable_snd
-/
theorem snd_mono {μ : Measure (α × β)} (h : ρ <= μ) : ρ.snd <= μ.snd := map_mono h measurable_snd

/--
lemma `fst_map_swap` / 引理 `fst_map_swap`

English:
lemma fst_map_swap
  statement: (ρ.map Prod.swap).fst = ρ.snd
  proof: by
  rw [Measure.fst]; rw [Measure.map_map measurable_fst measurable_swap]
  rfl

中文:
引理 fst_map_swap
  结论: (ρ.map 积类型.swap).fst = ρ.snd
  证明: by
  rw [Measure.fst]; rw [Measure.map_map measurable_fst measurable_swap]
  rfl
-/
@[simp] lemma fst_map_swap : (ρ.map Prod.swap).fst = ρ.snd := by
  rw [Measure.fst]; rw [Measure.map_map measurable_fst measurable_swap]
  rfl

/--
lemma `snd_map_swap` / 引理 `snd_map_swap`

English:
lemma snd_map_swap
  statement: (ρ.map Prod.swap).snd = ρ.fst
  proof: by
  rw [Measure.snd]; rw [Measure.map_map measurable_snd measurable_swap]
  rfl

中文:
引理 snd_map_swap
  结论: (ρ.map 积类型.swap).snd = ρ.fst
  证明: by
  rw [Measure.snd]; rw [Measure.map_map measurable_snd measurable_swap]
  rfl
-/
@[simp] lemma snd_map_swap : (ρ.map Prod.swap).snd = ρ.fst := by
  rw [Measure.snd]; rw [Measure.map_map measurable_snd measurable_swap]
  rfl

end Measure

section MeasurePreserving

-- Note that these results cannot be put in the previous `measurePreserving` section since
-- they use `lintegral_prod`.

/--
theorem `_root_.MeasureTheory.measurePreserving_prodAssoc` / 定理 `_root_.MeasureTheory.measurePreserving_prodAssoc`

English:
theorem _root_.MeasureTheory.measurePreserving_prodAssoc
  statement: (μa : Measure α) (μb : Measure β)
  proof: MeasurableEquiv.prodAssoc.measurable
  map_eq := by
    ext s hs
    have A (x : α) : MeasurableSet (Prod.mk x ⁻¹' s) := measurable_prodMk_left hs
    have B : MeasurableSet (MeasurableEquiv.prodAssoc ⁻¹' s) :=
      MeasurableEquiv.prodAssoc.measurable hs
    simp_rw [map_apply MeasurableEquiv.prod

中文:
定理 _root_.测度论.measurePreserving_prodAssoc
  结论: (μa : 测度 α) (μb : 测度 β)
  证明: MeasurableEquiv.prodAssoc.measurable
  map_eq := by
    ext s hs
    have A (x : α) : MeasurableSet (Prod.mk x ⁻¹' s) := measurable_prodMk_left hs
    have B : MeasurableSet (MeasurableEquiv.prodAssoc ⁻¹' s) :=
      MeasurableEquiv.prodAssoc.measurable hs
    simp_rw [map_apply MeasurableEquiv.prod

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.prodAssoc.measurable, measurable, prodAssoc
-/
theorem _root_.MeasureTheory.measurePreserving_prodAssoc (μa : Measure α) (μb : Measure β)
    (μc : Measure γ) [SFinite μb] [SFinite μc] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ)
      ((μa.prod μb).prod μc) (μa.prod (μb.prod μc)) where
  measurable := MeasurableEquiv.prodAssoc.measurable
  map_eq := by
    ext s hs
    have A (x : α) : MeasurableSet (Prod.mk x ⁻¹' s) := measurable_prodMk_left hs
    have B : MeasurableSet (MeasurableEquiv.prodAssoc ⁻¹' s) :=
      MeasurableEquiv.prodAssoc.measurable hs
    simp_rw [map_apply MeasurableEquiv.prodAssoc.measurable hs, Measure.prod_apply hs,
    Measure.prod_apply (A _), Measure.prod_apply B,
    lintegral_prod _ (measurable_measure_prodMk_left B).aemeasurable]
    rfl

/--
theorem `_root_.MeasureTheory.volume_preserving_prodAssoc` / 定理 `_root_.MeasureTheory.volume_preserving_prodAssoc`

English:
theorem _root_.MeasureTheory.volume_preserving_prodAssoc
  statement: {α₁ β₁ γ₁ : Type*} [MeasureSpace α₁]
  proof: MeasureTheory.measurePreserving_prodAssoc volume volume volume

中文:
定理 _root_.测度论.volume_preserving_prodAssoc
  结论: {α₁ β₁ γ₁ : 类型} [测度空间 α₁]
  证明: MeasureTheory.measurePreserving_prodAssoc volume volume volume

Depends on / 依赖: MeasureTheory, MeasureTheory.measurePreserving_prodAssoc, measurePreserving_prodAssoc, volume
-/
theorem _root_.MeasureTheory.volume_preserving_prodAssoc {α₁ β₁ γ₁ : Type*} [MeasureSpace α₁]
    [MeasureSpace β₁] [MeasureSpace γ₁] [SFinite (volume : Measure β₁)]
    [SFinite (volume : Measure γ₁)] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α₁ × β₁) × γ₁ ≃ᵐ α₁ × β₁ × γ₁) :=
  MeasureTheory.measurePreserving_prodAssoc volume volume volume

end MeasurePreserving

end MeasureTheory
