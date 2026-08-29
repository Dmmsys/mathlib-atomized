/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The multiplicative and additive convolution of measures

In this file we define and prove properties about the convolutions of two measures.

## Main definitions

* `MeasureTheory.Measure.mconv`: The multiplicative convolution of two measures: the map of `*`
  under the product measure.
* `MeasureTheory.Measure.conv`: The additive convolution of two measures: the map of `+`
  under the product measure.
-/

@[expose] public section

namespace MeasureTheory

namespace Measure
open scoped ENNReal

variable {M : Type*} [Monoid M] [MeasurableSpace M]

/-- Multiplicative convolution of measures. -/
@[to_additive /-- Additive convolution of measures. -/]
/--
Definition of `mconv` / `mconv` 的定义

English:
definition mconv
  signature: (μ : Measure M) (ν : Measure M)
  body: Measure.map (fun x : M × M => x.1 * x.2) (μ.prod ν)

中文:
定义 mconv
  签名: (μ : 测度 M) (ν : 测度 M)
  定义体: Measure.map (fun x : M × M => x.1 * x.2) (μ.prod ν)

Depends on / 依赖: Measure, Measure.map
-/
noncomputable def mconv (μ : Measure M) (ν : Measure M) :
    Measure M := Measure.map (fun x : M × M => x.1 * x.2) (μ.prod ν)

/-- Scoped notation for the multiplicative convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ₘ " => MeasureTheory.Measure.mconv

/-- Scoped notation for the additive convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ " => MeasureTheory.Measure.conv

@[to_additive]
/--
theorem `lintegral_mconv_eq_lintegral_prod` / 定理 `lintegral_mconv_eq_lintegral_prod`

English:
theorem lintegral_mconv_eq_lintegral_prod
  statement: [MeasurableMul₂ M] {μ ν : Measure M}
  proof: by
  rw [mconv]; rw [lintegral_map hf measurable_mul]

@[to_additive]

中文:
定理 lintegral_mconv_eq_lintegral_prod
  结论: [MeasurableMul₂ M] {μ ν : 测度 M}
  证明: by
  rw [mconv]; rw [lintegral_map hf measurable_mul]

@[to_additive]

Depends on / 依赖: lintegral_map, measurable_mul
-/
theorem lintegral_mconv_eq_lintegral_prod [MeasurableMul₂ M] {μ ν : Measure M}
    {f : M -> Real>=0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ z, f (z.1 * z.2) ∂(μ.prod ν) := by
  rw [mconv]; rw [lintegral_map hf measurable_mul]

@[to_additive]
/--
theorem `lintegral_mconv` / 定理 `lintegral_mconv`

English:
theorem lintegral_mconv
  statement: [MeasurableMul₂ M] {μ ν : Measure M} [SFinite ν]
  proof: by
  rw [lintegral_mconv_eq_lintegral_prod hf]; rw [lintegral_prod _ (by fun_prop)]

@[to_additive]

中文:
定理 lintegral_mconv
  结论: [MeasurableMul₂ M] {μ ν : 测度 M} [SFinite ν]
  证明: by
  rw [lintegral_mconv_eq_lintegral_prod hf]; rw [lintegral_prod _ (by fun_prop)]

@[to_additive]

Depends on / 依赖: fun_prop, lintegral_mconv_eq_lintegral_prod, lintegral_prod
-/
theorem lintegral_mconv [MeasurableMul₂ M] {μ ν : Measure M} [SFinite ν]
    {f : M -> Real>=0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ x, ∫⁻ y, f (x * y) ∂ν ∂μ := by
  rw [lintegral_mconv_eq_lintegral_prod hf]; rw [lintegral_prod _ (by fun_prop)]

@[to_additive]
/--
lemma `dirac_mconv` / 引理 `dirac_mconv`

English:
lemma dirac_mconv
  given: [MeasurableMul₂ M] (x : M) (μ : Measure M) [SFinite μ]
  proof: by
  unfold mconv
  rw [dirac_prod]; rw [map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

@[to_additive]

中文:
引理 dirac_mconv
  条件: [MeasurableMul₂ M] (x : M) (μ : 测度 M) [SFinite μ]
  证明: by
  unfold mconv
  rw [dirac_prod]; rw [map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comp_def, dirac_prod, fun_prop, map_map
-/
lemma dirac_mconv [MeasurableMul₂ M] (x : M) (μ : Measure M) [SFinite μ] :
    (dirac x) ∗ₘ μ = μ.map (fun y => x * y) := by
  unfold mconv
  rw [dirac_prod]; rw [map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

@[to_additive]
/--
lemma `mconv_dirac` / 引理 `mconv_dirac`

English:
lemma mconv_dirac
  given: [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] (x : M)
  proof: by
  unfold mconv
  rw [prod_dirac]; rw [map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

@[to_additive (attr := simp)]

中文:
引理 mconv_dirac
  条件: [MeasurableMul₂ M] (μ : 测度 M) [SFinite μ] (x : M)
  证明: by
  unfold mconv
  rw [prod_dirac]; rw [map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def, fun_prop, map_map, prod_dirac
-/
lemma mconv_dirac [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] (x : M) :
    μ ∗ₘ (dirac x) = μ.map (fun y => y * x) := by
  unfold mconv
  rw [prod_dirac]; rw [map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

@[to_additive (attr := simp)]
/--
lemma `dirac_mconv_dirac` / 引理 `dirac_mconv_dirac`

English:
lemma dirac_mconv_dirac
  given: [MeasurableMul₂ M] (x y : M)
  proof: by
  rw [mconv_dirac]; rw [map_dirac' (by fun_prop)]

中文:
引理 dirac_mconv_dirac
  条件: [MeasurableMul₂ M] (x y : M)
  证明: by
  rw [mconv_dirac]; rw [map_dirac' (by fun_prop)]

Depends on / 依赖: fun_prop, map_dirac, mconv_dirac
-/
lemma dirac_mconv_dirac [MeasurableMul₂ M] (x y : M) :
    (dirac x) ∗ₘ (dirac y) = dirac (x * y) := by
  rw [mconv_dirac]; rw [map_dirac' (by fun_prop)]

/-- Convolution of the dirac measure at 1 with a measure μ returns μ. -/
@[to_additive (attr := simp)
/-- Convolution of the dirac measure at 0 with a measure μ returns μ. -/]
/--
theorem `dirac_one_mconv` / 定理 `dirac_one_mconv`

English:
theorem dirac_one_mconv
  given: [MeasurableMul₂ M] (μ : Measure M) [SFinite μ]
  proof: by
  simp [dirac_mconv]

中文:
定理 dirac_one_mconv
  条件: [MeasurableMul₂ M] (μ : 测度 M) [SFinite μ]
  证明: by
  simp [dirac_mconv]

Depends on / 依赖: dirac_mconv
-/
theorem dirac_one_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] :
    (dirac 1) ∗ₘ μ = μ := by
  simp [dirac_mconv]

/-- Convolution of a measure μ with the dirac measure at 1 returns μ. -/
@[to_additive (attr := simp)
/-- Convolution of a measure μ with the dirac measure at 0 returns μ. -/]
/--
theorem `mconv_dirac_one` / 定理 `mconv_dirac_one`

English:
theorem mconv_dirac_one
  statement: [MeasurableMul₂ M]
  proof: by
  simp [mconv_dirac]

中文:
定理 mconv_dirac_one
  结论: [MeasurableMul₂ M]
  证明: by
  simp [mconv_dirac]

Depends on / 依赖: mconv_dirac
-/
theorem mconv_dirac_one [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : μ ∗ₘ (dirac 1) = μ := by
  simp [mconv_dirac]

/-- Convolution of the zero measure with a measure μ returns the zero measure. -/
@[to_additive (attr := simp) /-- Convolution of the zero measure with a measure μ returns
the zero measure. -/]
/--
theorem `zero_mconv` / 定理 `zero_mconv`

English:
theorem zero_mconv
  given: (μ : Measure M)
  statement: (0 : Measure M) ∗ₘ μ = (0 : Measure M)
  proof: by
  unfold mconv
  simp

中文:
定理 zero_mconv
  条件: (μ : 测度 M)
  结论: (0 : 测度 M) ∗ₘ μ = (0 : 测度 M)
  证明: by
  unfold mconv
  simp
-/
theorem zero_mconv (μ : Measure M) : (0 : Measure M) ∗ₘ μ = (0 : Measure M) := by
  unfold mconv
  simp

/-- Convolution of a measure μ with the zero measure returns the zero measure. -/
@[to_additive (attr := simp) /-- Convolution of a measure μ with the zero measure returns the zero
measure. -/]
/--
theorem `mconv_zero` / 定理 `mconv_zero`

English:
theorem mconv_zero
  given: (μ : Measure M)
  statement: μ ∗ₘ (0 : Measure M) = (0 : Measure M)
  proof: by
  unfold mconv
  simp

中文:
定理 mconv_zero
  条件: (μ : 测度 M)
  结论: μ ∗ₘ (0 : 测度 M) = (0 : 测度 M)
  证明: by
  unfold mconv
  simp
-/
theorem mconv_zero (μ : Measure M) : μ ∗ₘ (0 : Measure M) = (0 : Measure M) := by
  unfold mconv
  simp

-- `mconv_smul_right` needs an instance to get `SFinite (c • ν)` from `SFinite ν`,
-- hence it is placed in the `WithDensity` file, where the instance is defined.
@[to_additive conv_smul_left]
/--
theorem `mconv_smul_left` / 定理 `mconv_smul_left`

English:
theorem mconv_smul_left
  given: (μ : Measure M) (ν : Measure M) [SFinite ν] (s : Real>=0∞)
  proof: by
  unfold mconv
  rw [← Measure.map_smul]; rw [Measure.prod_smul_left]

@[to_additive]

中文:
定理 mconv_smul_left
  条件: (μ : 测度 M) (ν : 测度 M) [SFinite ν] (s : 实数>=0∞)
  证明: by
  unfold mconv
  rw [← Measure.map_smul]; rw [Measure.prod_smul_left]

@[to_additive]

Depends on / 依赖: Measure, Measure.map_smul, Measure.prod_smul_left, map_smul, prod_smul_left
-/
theorem mconv_smul_left (μ : Measure M) (ν : Measure M) [SFinite ν] (s : Real>=0∞) :
    (s • μ) ∗ₘ ν = s • (μ ∗ₘ ν) := by
  unfold mconv
  rw [← Measure.map_smul]; rw [Measure.prod_smul_left]

@[to_additive]
/--
theorem `mconv_add` / 定理 `mconv_add`

English:
theorem mconv_add
  statement: [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
  proof: by
  unfold mconv
  rw [prod_add]; rw [Measure.map_add]
  fun_prop

@[to_additive]

中文:
定理 mconv_add
  结论: [MeasurableMul₂ M] (μ : 测度 M) (ν : 测度 M) (ρ : 测度 M) [SFinite μ]
  证明: by
  unfold mconv
  rw [prod_add]; rw [Measure.map_add]
  fun_prop

@[to_additive]

Depends on / 依赖: Measure, Measure.map_add, fun_prop, map_add, prod_add
-/
theorem mconv_add [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : μ ∗ₘ (ν + ρ) = μ ∗ₘ ν + μ ∗ₘ ρ := by
  unfold mconv
  rw [prod_add]; rw [Measure.map_add]
  fun_prop

@[to_additive]
/--
theorem `add_mconv` / 定理 `add_mconv`

English:
theorem add_mconv
  statement: [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
  proof: by
  unfold mconv
  rw [add_prod]; rw [Measure.map_add]
  fun_prop

中文:
定理 add_mconv
  结论: [MeasurableMul₂ M] (μ : 测度 M) (ν : 测度 M) (ρ : 测度 M) [SFinite μ]
  证明: by
  unfold mconv
  rw [add_prod]; rw [Measure.map_add]
  fun_prop

Depends on / 依赖: Measure, Measure.map_add, add_prod, fun_prop, map_add
-/
theorem add_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : (μ + ν) ∗ₘ ρ = μ ∗ₘ ρ + ν ∗ₘ ρ := by
  unfold mconv
  rw [add_prod]; rw [Measure.map_add]
  fun_prop

/-- To get commutativity, we need the underlying multiplication to be commutative. -/
@[to_additive /-- To get commutativity, we need the underlying addition to be commutative. -/]
/--
theorem `mconv_comm` / 定理 `mconv_comm`

English:
theorem mconv_comm
  statement: {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M] (μ : Measure M)
  proof: by
  unfold mconv
  rw [← prod_swap]; rw [map_map (by fun_prop)]
  · simp [Function.comp_def, mul_comm]
  fun_prop

中文:
定理 mconv_comm
  结论: {M : 类型} [交换幺半群 M] [可测空间 M] [MeasurableMul₂ M] (μ : 测度 M)
  证明: by
  unfold mconv
  rw [← prod_swap]; rw [map_map (by fun_prop)]
  · simp [Function.comp_def, mul_comm]
  fun_prop

Depends on / 依赖: Function, Function.comp_def, comp_def, fun_prop, map_map, mul_comm, prod_swap
-/
theorem mconv_comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M] (μ : Measure M)
    (ν : Measure M) [SFinite μ] [SFinite ν] : μ ∗ₘ ν = ν ∗ₘ μ := by
  unfold mconv
  rw [← prod_swap]; rw [map_map (by fun_prop)]
  · simp [Function.comp_def, mul_comm]
  fun_prop

/-- The convolution of s-finite measures is s-finite. -/
@[to_additive /-- The convolution of s-finite measures is s-finite. -/]
/--
Instance `sfinite_mconv_of_sfinite` / 实例 `sfinite_mconv_of_sfinite`

English:
instance sfinite_mconv_of_sfinite
  signature: (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν]
  body: inferInstanceAs SFinite ((μ.prod ν).map fun (x : M × M) => x.1 * x.2)

@[to_additive]

中文:
实例 sfinite_mconv_of_sfinite
  签名: (μ : 测度 M) (ν : 测度 M) [SFinite μ] [SFinite ν]
  定义体: inferInstanceAs SFinite ((μ.prod ν).map fun (x : M × M) => x.1 * x.2)

@[to_additive]

Depends on / 依赖: SFinite
-/
instance sfinite_mconv_of_sfinite (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] :
SFinite (μ ∗ₘ ν) := inferInstanceAs SFinite ((μ.prod ν).map fun (x : M × M) => x.1 * x.2)

@[to_additive]
/--
Instance `finite_of_finite_mconv` / 实例 `finite_of_finite_mconv`

English:
instance finite_of_finite_mconv
  signature: (μ : Measure M) (ν : Measure M) [IsFiniteMeasure μ]
  body: by
  have h : (μ ∗ₘ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact { measure_univ_lt_top := h }

中文:
实例 finite_of_finite_mconv
  签名: (μ : 测度 M) (ν : 测度 M) [是有限测度 μ]
  定义体: by
  have h : (μ ∗ₘ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact { measure_univ_lt_top := h }

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.measure_univ_lt_top, Set.univ, measure_univ_lt_top
-/
instance finite_of_finite_mconv (μ : Measure M) (ν : Measure M) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : IsFiniteMeasure (μ ∗ₘ ν) := by
  have h : (μ ∗ₘ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact { measure_univ_lt_top := h }

/-- Convolution is associative. -/
@[to_additive /-- Convolution is associative. -/]
/--
theorem `mconv_assoc` / 定理 `mconv_assoc`

English:
theorem mconv_assoc
  statement: [MeasurableMul₂ M] (μ ν ρ : Measure M)
  proof: by
  refine ext_of_lintegral _ fun f hf => ?_
  repeat rw [lintegral_mconv (by fun_prop)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_mconv (by fun_prop)]
  repeat refine lintegral_congr fun x => ?_
  simp [mul_assoc]

@[to_additive]

中文:
定理 mconv_assoc
  结论: [MeasurableMul₂ M] (μ ν ρ : 测度 M)
  证明: by
  refine ext_of_lintegral _ fun f hf => ?_
  repeat rw [lintegral_mconv (by fun_prop)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_mconv (by fun_prop)]
  repeat refine lintegral_congr fun x => ?_
  simp [mul_assoc]

@[to_additive]

Depends on / 依赖: ext_of_lintegral, fun_prop, lintegral_congr, lintegral_mconv, mul_assoc, repeat
-/
theorem mconv_assoc [MeasurableMul₂ M] (μ ν ρ : Measure M)
    [SFinite ν] [SFinite ρ] :
    (μ ∗ₘ ν) ∗ₘ ρ = μ ∗ₘ (ν ∗ₘ ρ) := by
  refine ext_of_lintegral _ fun f hf => ?_
  repeat rw [lintegral_mconv (by fun_prop)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_mconv (by fun_prop)]
  repeat refine lintegral_congr fun x => ?_
  simp [mul_assoc]

@[to_additive]
/--
Instance `probabilitymeasure_of_probabilitymeasures_mconv` / 实例 `probabilitymeasure_of_probabilitymeasures_mconv`

English:
instance probabilitymeasure_of_probabilitymeasures_mconv
  signature: (μ : Measure M) (ν : Measure M)
  body: isProbabilityMeasure_map (by fun_prop)

@[to_additive]

中文:
实例 probabilitymeasure_of_probabilitymeasures_mconv
  签名: (μ : 测度 M) (ν : 测度 M)
  定义体: isProbabilityMeasure_map (by fun_prop)

@[to_additive]

Depends on / 依赖: fun_prop, isProbabilityMeasure_map
-/
instance probabilitymeasure_of_probabilitymeasures_mconv (μ : Measure M) (ν : Measure M)
    [MeasurableMul₂ M] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ ∗ₘ ν) :=
  isProbabilityMeasure_map (by fun_prop)

@[to_additive]
/--
theorem `mconv_absolutelyContinuous` / 定理 `mconv_absolutelyContinuous`

English:
theorem mconv_absolutelyContinuous
  statement: [MeasurableMul₂ M] {μ ν ρ : Measure M}
  proof: by
  refine AbsolutelyContinuous.mk (fun s hs h => ?_)
  rw [← lintegral_indicator_one hs]; rw [lintegral_mconv (by measurability)]
  conv in s.indicator 1 (_ * _) => change s.indicator 1 ((fun y => x * y) y)
  simp only [← Set.indicator_comp_right, Pi.one_comp]
  conv in ∫⁻ _, _ ∂ν =>
    rw [linte

中文:
定理 mconv_absolutelyContinuous
  结论: [MeasurableMul₂ M] {μ ν ρ : 测度 M}
  证明: by
  refine AbsolutelyContinuous.mk (fun s hs h => ?_)
  rw [← lintegral_indicator_one hs]; rw [lintegral_mconv (by measurability)]
  conv in s.indicator 1 (_ * _) => change s.indicator 1 ((fun y => x * y) y)
  simp only [← Set.indicator_comp_right, Pi.one_comp]
  conv in ∫⁻ _, _ ∂ν =>
    rw [linte

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, HMul.hMul, IsMulLeftInvariant, IsMulLeftInvariant.map_mul_left_eq_self, MeasurableSet, MeasurableSet.preimage, Pi.one_comp, Set.indicator_comp_right, fun_prop, indicator, indicator_comp_right, lintegral_indicator_one, lintegral_mconv, map_apply, map_mul_left_eq_self, measurability, one_comp, preimage, s.indicator
-/
theorem mconv_absolutelyContinuous [MeasurableMul₂ M] {μ ν ρ : Measure M}
    [IsMulLeftInvariant ρ] [SFinite ν] (hν : ν ≪ ρ) : μ ∗ₘ ν ≪ ρ := by
  refine AbsolutelyContinuous.mk (fun s hs h => ?_)
  rw [← lintegral_indicator_one hs]; rw [lintegral_mconv (by measurability)]
  conv in s.indicator 1 (_ * _) => change s.indicator 1 ((fun y => x * y) y)
  simp only [← Set.indicator_comp_right, Pi.one_comp]
  conv in ∫⁻ _, _ ∂ν =>
    rw [lintegral_indicator_one (by apply MeasurableSet.preimage hs (by fun_prop))]
  have h0 (x : M) : ν (HMul.hMul x ⁻¹' s) = 0 := by
    apply hν
    rw [← map_apply (by fun_prop) hs]; rw [IsMulLeftInvariant.map_mul_left_eq_self]; rw [h]
  simp [h0]

@[to_additive]
/--
lemma `map_mconv_monoidHom` / 引理 `map_mconv_monoidHom`

English:
lemma map_mconv_monoidHom
  statement: {M M' : Type*} {mM : MeasurableSpace M} [Monoid M] [MeasurableMul₂ M]
  proof: by
  unfold mconv
  rw [map_map (by fun_prop) (by fun_prop)]
  have : (L ∘ fun p : M × M => p.1 * p.2) = (fun p : M' × M' => p.1 * p.2) ∘ (Prod.map L L) := by
    ext; simp
  rw [this]; rw [← map_map (by fun_prop) (by fun_prop)]; rw [← map_prod_map _ _ (by fun_prop) (by fun_prop)]

中文:
引理 map_mconv_monoidHom
  结论: {M M' : 类型} {mM : 可测空间 M} [幺半群 M] [MeasurableMul₂ M]
  证明: by
  unfold mconv
  rw [map_map (by fun_prop) (by fun_prop)]
  have : (L ∘ fun p : M × M => p.1 * p.2) = (fun p : M' × M' => p.1 * p.2) ∘ (Prod.map L L) := by
    ext; simp
  rw [this]; rw [← map_map (by fun_prop) (by fun_prop)]; rw [← map_prod_map _ _ (by fun_prop) (by fun_prop)]

Depends on / 依赖: Prod.map, fun_prop, map_map, map_prod_map
-/
lemma map_mconv_monoidHom {M M' : Type*} {mM : MeasurableSpace M} [Monoid M] [MeasurableMul₂ M]
    {mM' : MeasurableSpace M'} [Monoid M'] [MeasurableMul₂ M']
    {μ ν : Measure M} [SFinite μ] [SFinite ν]
    (L : M ->* M') (hL : Measurable L) :
    (μ ∗ₘ ν).map L = (μ.map L) ∗ₘ (ν.map L) := by
  unfold mconv
  rw [map_map (by fun_prop) (by fun_prop)]
  have : (L ∘ fun p : M × M => p.1 * p.2) = (fun p : M' × M' => p.1 * p.2) ∘ (Prod.map L L) := by
    ext; simp
  rw [this]; rw [← map_map (by fun_prop) (by fun_prop)]; rw [← map_prod_map _ _ (by fun_prop) (by fun_prop)]

/--
lemma `map_conv_continuousLinearMap` / 引理 `map_conv_continuousLinearMap`

English:
lemma map_conv_continuousLinearMap
  statement: {E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
  proof: by
  suffices (μ ∗ ν).map (L : E ->+ F) = (μ.map (L : E ->+ F)) ∗ (ν.map (L : E ->+ F)) by simpa
  rw [map_conv_addMonoidHom]
  rw [AddMonoidHom.coe_coe]
  fun_prop

中文:
引理 map_conv_continuousLinearMap
  结论: {E F : 类型} [加法交换幺半群 E] [加法交换幺半群 F]
  证明: by
  suffices (μ ∗ ν).map (L : E ->+ F) = (μ.map (L : E ->+ F)) ∗ (ν.map (L : E ->+ F)) by simpa
  rw [map_conv_addMonoidHom]
  rw [AddMonoidHom.coe_coe]
  fun_prop

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, coe_coe, fun_prop, map_conv_addMonoidHom
-/
lemma map_conv_continuousLinearMap {E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
    [Module Real E] [Module Real F] [TopologicalSpace E] [TopologicalSpace F]
    {mE : MeasurableSpace E} [MeasurableAdd₂ E] {mF : MeasurableSpace F} [MeasurableAdd₂ F]
    [OpensMeasurableSpace E] [BorelSpace F]
    {μ ν : Measure E} [SFinite μ] [SFinite ν]
    (L : E ->L[Real] F) :
    (μ ∗ ν).map L = (μ.map L) ∗ (ν.map L) := by
  suffices (μ ∗ ν).map (L : E ->+ F) = (μ.map (L : E ->+ F)) ∗ (ν.map (L : E ->+ F)) by simpa
  rw [map_conv_addMonoidHom]
  rw [AddMonoidHom.coe_coe]
  fun_prop

end Measure

end MeasureTheory
