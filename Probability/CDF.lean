/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Disintegration.CondCDF
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cumulative distribution function of a real probability measure

The cumulative distribution function (cdf) of a probability measure over `ℝ` is a monotone, right
continuous function with limit 0 at -∞ and 1 at +∞, such that `cdf μ x = μ (Iic x)` for all `x : ℝ`.
Two probability measures are equal if and only if they have the same cdf.

## Main definitions

* `ProbabilityTheory.cdf μ`: cumulative distribution function of `μ : Measure ℝ`, defined as the
  conditional cdf (`ProbabilityTheory.condCDF`) of the product measure
  `(Measure.dirac Unit.unit).prod μ` evaluated at `Unit.unit`.

The definition could be replaced by the more elementary `cdf μ x = μ.real (Iic x)`, but using
`condCDF` gives us access to its API, from which most properties of the cdf follow directly.

## Main statements

* `ProbabilityTheory.ofReal_cdf`: for a probability measure `μ` and `x : ℝ`,
  `ENNReal.ofReal (cdf μ x) = μ (Iic x)`.
* `MeasureTheory.Measure.ext_of_cdf`: two probability measures are equal if and only if they have
  the same cdf.

## TODO

The definition could be extended to a finite measure by rescaling `condCDF`, but it would be nice
to have more structure on Stieltjes functions first. Right now, if `f` is a Stieltjes function,
`2 • f` makes no sense. We could define Stieltjes functions as a submodule.

The definition could be extended to `ℝⁿ`, either by extending the definition of `condCDF`, or by
using another construction here.
-/

@[expose] public section

open MeasureTheory Measure Set Filter

open scoped Topology

namespace ProbabilityTheory

/-- Cumulative distribution function of a real measure. The definition currently makes sense only
for probability measures. In that case, it satisfies `cdf μ x = μ.real (Iic x)` (see
`ProbabilityTheory.cdf_eq_real`). -/
@[wikidata Q386228]
noncomputable
/--
Definition of `cdf` / `cdf` 的定义

English:
definition cdf
  signature: (μ : Measure Real)
  body: condCDF ((dirac Unit.unit).prod μ) Unit.unit

中文:
定义 cdf
  签名: (μ : 测度 实数)
  定义体: condCDF ((dirac Unit.unit).prod μ) Unit.unit

Depends on / 依赖: Unit.unit, condCDF
-/
def cdf (μ : Measure Real) : StieltjesFunction Real :=
  condCDF ((dirac Unit.unit).prod μ) Unit.unit

section ExplicitMeasureArg
variable (μ : Measure Real)

/--
lemma `cdf_nonneg` / 引理 `cdf_nonneg`

English:
lemma cdf_nonneg
  given: (x : Real)
  statement: 0 <= cdf μ x
  proof: condCDF_nonneg _ _ _

中文:
引理 cdf_nonneg
  条件: (x : 实数)
  结论: 0 <= cdf μ x
  证明: condCDF_nonneg _ _ _

Depends on / 依赖: condCDF_nonneg
-/
lemma cdf_nonneg (x : Real) : 0 <= cdf μ x := condCDF_nonneg _ _ _

/--
lemma `cdf_le_one` / 引理 `cdf_le_one`

English:
lemma cdf_le_one
  given: (x : Real)
  statement: cdf μ x <= 1
  proof: condCDF_le_one _ _ _

中文:
引理 cdf_le_one
  条件: (x : 实数)
  结论: cdf μ x <= 1
  证明: condCDF_le_one _ _ _

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, condCDF_le_one, ha.symm
-/
lemma cdf_le_one (x : Real) : cdf μ x <= 1 := condCDF_le_one _ _ _

/--
lemma `monotone_cdf` / 引理 `monotone_cdf`

English:
lemma monotone_cdf
  statement: Monotone (cdf μ)
  proof: (condCDF _ _).mono

中文:
引理 monotone_cdf
  结论: 递增 (cdf μ)
  证明: (condCDF _ _).mono

Depends on / 依赖: condCDF
-/
lemma monotone_cdf : Monotone (cdf μ) := (condCDF _ _).mono

/--
lemma `tendsto_cdf_atBot` / 引理 `tendsto_cdf_atBot`

English:
lemma tendsto_cdf_atBot
  statement: Tendsto (cdf μ) atBot (𝓝 0)
  proof: tendsto_condCDF_atBot _ _

中文:
引理 tendsto_cdf_atBot
  结论: 收敛 (cdf μ) atBot (𝓝 0)
  证明: tendsto_condCDF_atBot _ _

Depends on / 依赖: tendsto_condCDF_atBot
-/
lemma tendsto_cdf_atBot : Tendsto (cdf μ) atBot (𝓝 0) := tendsto_condCDF_atBot _ _

/--
lemma `tendsto_cdf_atTop` / 引理 `tendsto_cdf_atTop`

English:
lemma tendsto_cdf_atTop
  statement: Tendsto (cdf μ) atTop (𝓝 1)
  proof: tendsto_condCDF_atTop _ _

中文:
引理 tendsto_cdf_atTop
  结论: 收敛 (cdf μ) atTop (𝓝 1)
  证明: tendsto_condCDF_atTop _ _

Depends on / 依赖: tendsto_condCDF_atTop
-/
lemma tendsto_cdf_atTop : Tendsto (cdf μ) atTop (𝓝 1) := tendsto_condCDF_atTop _ _

/--
lemma `ofReal_cdf` / 引理 `ofReal_cdf`

English:
lemma ofReal_cdf
  given: [IsProbabilityMeasure μ] (x : Real)
  statement: ENNReal.ofReal (cdf μ x) = μ (Iic x)
  proof: by
  have h := lintegral_condCDF ((dirac Unit.unit).prod μ) x
  simpa only [fst_prod, prod_prod, measure_univ, one_mul, lintegral_dirac] using! h

中文:
引理 of实数_cdf
  条件: [是概率测度 μ] (x : 实数)
  结论: 广义非负实数.of实数 (cdf μ x) = μ (左无界右闭区间 x)
  证明: by
  have h := lintegral_condCDF ((dirac Unit.unit).prod μ) x
  simpa only [fst_prod, prod_prod, measure_univ, one_mul, lintegral_dirac] using! h

Depends on / 依赖: Unit.unit, fst_prod, lintegral_condCDF, lintegral_dirac, measure_univ, one_mul, prod_prod
-/
lemma ofReal_cdf [IsProbabilityMeasure μ] (x : Real) : ENNReal.ofReal (cdf μ x) = μ (Iic x) := by
  have h := lintegral_condCDF ((dirac Unit.unit).prod μ) x
  simpa only [fst_prod, prod_prod, measure_univ, one_mul, lintegral_dirac] using! h

/--
lemma `cdf_eq_real` / 引理 `cdf_eq_real`

English:
lemma cdf_eq_real
  given: [IsProbabilityMeasure μ] (x : Real)
  statement: cdf μ x = μ.real (Iic x)
  proof: by
  rw [measureReal_def]; rw [← ofReal_cdf μ x]; rw [ENNReal.toReal_ofReal (cdf_nonneg μ x)]

中文:
引理 cdf_eq_real
  条件: [是概率测度 μ] (x : 实数)
  结论: cdf μ x = μ.real (左无界右闭区间 x)
  证明: by
  rw [measureReal_def]; rw [← ofReal_cdf μ x]; rw [ENNReal.toReal_ofReal (cdf_nonneg μ x)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, cdf_nonneg, measureReal_def, ofReal_cdf, toReal_ofReal
-/
lemma cdf_eq_real [IsProbabilityMeasure μ] (x : Real) : cdf μ x = μ.real (Iic x) := by
  rw [measureReal_def]; rw [← ofReal_cdf μ x]; rw [ENNReal.toReal_ofReal (cdf_nonneg μ x)]

/--
Instance `instIsProbabilityMeasurecdf` / 实例 `instIsProbabilityMeasurecdf`

English:
instance instIsProbabilityMeasurecdf
  signature: : IsProbabilityMeasure (cdf μ).measure
  body: by
  constructor
  simp only [StieltjesFunction.measure_univ _ (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ), sub_zero,
    ENNReal.ofReal_one]

中文:
实例 instIsProbabilityMeasurecdf
  签名: : 是概率测度 (cdf μ).measure
  定义体: by
  constructor
  simp only [StieltjesFunction.measure_univ _ (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ), sub_zero,
    ENNReal.ofReal_one]

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, StieltjesFunction, StieltjesFunction.measure_univ, measure_univ, ofReal_one, sub_zero, tendsto_cdf_atBot, tendsto_cdf_atTop
-/
instance instIsProbabilityMeasurecdf : IsProbabilityMeasure (cdf μ).measure := by
  constructor
  simp only [StieltjesFunction.measure_univ _ (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ), sub_zero,
    ENNReal.ofReal_one]

/--
lemma `measure_cdf` / 引理 `measure_cdf`

English:
lemma measure_cdf
  given: [IsProbabilityMeasure μ]
  statement: (cdf μ).measure = μ
  proof: by
  refine ext_of_Iic (cdf μ).measure μ (fun a => ?_)
  rw [StieltjesFunction.measure_Iic _ (tendsto_cdf_atBot μ)]; rw [sub_zero]; rw [ofReal_cdf]

中文:
引理 measure_cdf
  条件: [是概率测度 μ]
  结论: (cdf μ).measure = μ
  证明: by
  refine ext_of_Iic (cdf μ).measure μ (fun a => ?_)
  rw [StieltjesFunction.measure_Iic _ (tendsto_cdf_atBot μ)]; rw [sub_zero]; rw [ofReal_cdf]

Depends on / 依赖: StieltjesFunction, StieltjesFunction.measure_Iic, ext_of_Iic, measure, measure_Iic, ofReal_cdf, sub_zero, tendsto_cdf_atBot
-/
lemma measure_cdf [IsProbabilityMeasure μ] : (cdf μ).measure = μ := by
  refine ext_of_Iic (cdf μ).measure μ (fun a => ?_)
  rw [StieltjesFunction.measure_Iic _ (tendsto_cdf_atBot μ)]; rw [sub_zero]; rw [ofReal_cdf]

end ExplicitMeasureArg

/--
lemma `cdf_measure_stieltjesFunction` / 引理 `cdf_measure_stieltjesFunction`

English:
lemma cdf_measure_stieltjesFunction
  statement: (f : StieltjesFunction Real) (hf0 : Tendsto f atBot (𝓝 0))
  proof: by
  refine (cdf f.measure).eq_of_measure_of_tendsto_atBot f ?_ (tendsto_cdf_atBot _) hf0
  have h_prob : IsProbabilityMeasure f.measure :=
    ⟨by rw [f.measure_univ hf0 hf1, sub_zero, ENNReal.ofReal_one]⟩
  exact measure_cdf f.measure

中文:
引理 cdf_measure_stieltjesFunction
  结论: (f : Stieltjes函数 实数) (hf0 : 收敛 f atBot (𝓝 0))
  证明: by
  refine (cdf f.measure).eq_of_measure_of_tendsto_atBot f ?_ (tendsto_cdf_atBot _) hf0
  have h_prob : IsProbabilityMeasure f.measure :=
    ⟨by rw [f.measure_univ hf0 hf1, sub_zero, ENNReal.ofReal_one]⟩
  exact measure_cdf f.measure

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, IsProbabilityMeasure, eq_of_measure_of_tendsto_atBot, f.measure, f.measure_univ, h_prob, measure, measure_cdf, measure_univ, ofReal_one, sub_zero, tendsto_cdf_atBot
-/
lemma cdf_measure_stieltjesFunction (f : StieltjesFunction Real) (hf0 : Tendsto f atBot (𝓝 0))
    (hf1 : Tendsto f atTop (𝓝 1)) :
    cdf f.measure = f := by
  refine (cdf f.measure).eq_of_measure_of_tendsto_atBot f ?_ (tendsto_cdf_atBot _) hf0
  have h_prob : IsProbabilityMeasure f.measure :=
    ⟨by rw [f.measure_univ hf0 hf1, sub_zero, ENNReal.ofReal_one]⟩
  exact measure_cdf f.measure

open unitInterval in
/--
lemma `unitInterval.cdf_eq_real` / 引理 `unitInterval.cdf_eq_real`

English:
lemma unitInterval.cdf_eq_real
  given: (μ : Measure I) [IsProbabilityMeasure μ] (x : I)
  proof: by
  have : IsProbabilityMeasure (μ.map Subtype.val) := isProbabilityMeasure_map (by fun_prop)
  rw [ProbabilityTheory.cdf_eq_real]; rw [map_measureReal_apply measurable_subtype_coe measurableSet_Iic]; rw [subtype_Iic_eq_Icc]

中文:
引理 unit整数erval.cdf_eq_real
  条件: (μ : 测度 I) [是概率测度 μ] (x : I)
  证明: by
  have : IsProbabilityMeasure (μ.map Subtype.val) := isProbabilityMeasure_map (by fun_prop)
  rw [ProbabilityTheory.cdf_eq_real]; rw [map_measureReal_apply measurable_subtype_coe measurableSet_Iic]; rw [subtype_Iic_eq_Icc]

Depends on / 依赖: IsProbabilityMeasure, ProbabilityTheory, ProbabilityTheory.cdf_eq_real, Subtype, Subtype.val, cdf_eq_real, fun_prop, isProbabilityMeasure_map, map_measureReal_apply, measurableSet_Iic, measurable_subtype_coe, subtype_Iic_eq_Icc
-/
lemma unitInterval.cdf_eq_real (μ : Measure I) [IsProbabilityMeasure μ] (x : I) :
    cdf (μ.map Subtype.val) x.1 = μ.real (Icc 0 x) := by
  have : IsProbabilityMeasure (μ.map Subtype.val) := isProbabilityMeasure_map (by fun_prop)
  rw [ProbabilityTheory.cdf_eq_real]; rw [map_measureReal_apply measurable_subtype_coe measurableSet_Iic]; rw [subtype_Iic_eq_Icc]

end ProbabilityTheory

open ProbabilityTheory

/--
lemma `MeasureTheory.Measure.eq_of_cdf` / 引理 `MeasureTheory.Measure.eq_of_cdf`

English:
lemma MeasureTheory.Measure.eq_of_cdf
  statement: (μ ν : Measure Real) [IsProbabilityMeasure μ]
  proof: by
  rw [← measure_cdf μ]; rw [← measure_cdf ν]; rw [h]

中文:
引理 测度论.测度.eq_of_cdf
  结论: (μ ν : 测度 实数) [是概率测度 μ]
  证明: by
  rw [← measure_cdf μ]; rw [← measure_cdf ν]; rw [h]

Depends on / 依赖: measure_cdf
-/
lemma MeasureTheory.Measure.eq_of_cdf (μ ν : Measure Real) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : cdf μ = cdf ν) : μ = ν := by
  rw [← measure_cdf μ]; rw [← measure_cdf ν]; rw [h]

/--
lemma `MeasureTheory.Measure.cdf_eq_iff` / 引理 `MeasureTheory.Measure.cdf_eq_iff`

English:
lemma MeasureTheory.Measure.cdf_eq_iff
  statement: (μ ν : Measure Real) [IsProbabilityMeasure μ]
  proof: ⟨eq_of_cdf μ ν, fun h => by rw [h]⟩

中文:
引理 测度论.测度.cdf_eq_iff
  结论: (μ ν : 测度 实数) [是概率测度 μ]
  证明: ⟨eq_of_cdf μ ν, fun h => by rw [h]⟩
-/
@[simp] lemma MeasureTheory.Measure.cdf_eq_iff (μ ν : Measure Real) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    cdf μ = cdf ν ↔ μ = ν :=
⟨eq_of_cdf μ ν, fun h => by rw [h]⟩
