/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurable parametric Stieltjes functions

We provide tools to build a measurable function `α → StieltjesFunction ℝ` with limits 0 at -∞
and 1 at +∞ for all `a : α` from a measurable function `f : α → ℚ → ℝ`. These measurable parametric
Stieltjes functions are cumulative distribution functions (CDF) of transition kernels.
The reason for going through `ℚ` instead of defining directly a Stieltjes function is that since
`ℚ` is countable, building a measurable function is easier and we can obtain properties of the
form `∀ᵐ (a : α) ∂μ, ∀ (q : ℚ), ...` (for some measure `μ` on `α`) by proving the weaker
`∀ (q : ℚ), ∀ᵐ (a : α) ∂μ, ...`.

This construction will be possible if `f a : ℚ → ℝ` satisfies a package of properties for all `a`:
monotonicity, limits at +-∞ and a continuity property. We define `IsRatStieltjesPoint f a` to state
that this is the case at `a` and define the property `IsMeasurableRatCDF f` that `f` is measurable
and `IsRatStieltjesPoint f a` for all `a`.
The function `α → StieltjesFunction ℝ` obtained by extending `f` by continuity from the right is
then called `IsMeasurableRatCDF.stieltjesFunction`.

In applications, we will often only have `IsRatStieltjesPoint f a` almost surely with respect to
some measure. In order to turn that almost everywhere property into an everywhere property we define
`toRatCDF (f : α → ℚ → ℝ) := fun a q ↦ if IsRatStieltjesPoint f a then f a q else defaultRatCDF q`,
which satisfies the property `IsMeasurableRatCDF (toRatCDF f)`.

Finally, we define `stieltjesOfMeasurableRat`, composition of `toRatCDF` and
`IsMeasurableRatCDF.stieltjesFunction`.

## Main definitions

* `stieltjesOfMeasurableRat`: turn a measurable function `f : α → ℚ → ℝ` into a measurable
  function `α → StieltjesFunction ℝ`.

-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

/--
lemma `StieltjesFunction.measurable_measure` / 引理 `StieltjesFunction.measurable_measure`

English:
lemma StieltjesFunction.measurable_measure
  statement: {α : Type*} {_ : MeasurableSpace α}
  proof: have : forall a, IsProbabilityMeasure (f a).measure :=
    fun a => (f a).isProbabilityMeasure (hf_bot a) (hf_top a)
.measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic Real) isPiSystem_Iic by
    simp_rw [forall_mem_range, StieltjesFunction.measure_Iic (f _) (hf_bot _), sub_ze

中文:
引理 Stieltjes函数.measurable_measure
  结论: {α : 类型} {_ : 可测空间 α}
  证明: have : forall a, IsProbabilityMeasure (f a).measure :=
    fun a => (f a).isProbabilityMeasure (hf_bot a) (hf_top a)
.measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic Real) isPiSystem_Iic by
    simp_rw [forall_mem_range, StieltjesFunction.measure_Iic (f _) (hf_bot _), sub_ze

Depends on / 依赖: IsProbabilityMeasure, StieltjesFunction, StieltjesFunction.measure_Iic, borel_eq_generateFrom_Iic, ennreal_ofReal, forall_mem_range, hf_bot, hf_top, isPiSystem_Iic, isProbabilityMeasure, measure, measure_Iic, measure_of_isPiSystem_of_isProbabilityMeasure, simp_rw, sub_zero
-/
lemma StieltjesFunction.measurable_measure {α : Type*} {_ : MeasurableSpace α}
    {f : α -> StieltjesFunction Real} (hf : forall q, Measurable fun a => f a q)
    (hf_bot : forall a, Tendsto (f a) atBot (𝓝 0))
    (hf_top : forall a, Tendsto (f a) atTop (𝓝 1)) :
    Measurable fun a => (f a).measure :=
  have : forall a, IsProbabilityMeasure (f a).measure :=
    fun a => (f a).isProbabilityMeasure (hf_bot a) (hf_top a)
.measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic Real) isPiSystem_Iic by
    simp_rw [forall_mem_range, StieltjesFunction.measure_Iic (f _) (hf_bot _), sub_zero]
    exact fun _ => (hf _).ennreal_ofReal

namespace ProbabilityTheory

variable {α : Type*}

section IsMeasurableRatCDF

variable {f : α -> Rat -> Real}

/--
Definition of `IsRatStieltjesPoint` / `IsRatStieltjesPoint` 的定义

English:
structure IsRatStieltjesPoint
  parameters: (f : α -> Rat -> Real) (a : α)
  axioms and operations (4):
    - mono : Monotone (f a)
    - tendsto_atTop_one : Tendsto (f a) atTop (𝓝 1)
    - tendsto_atBot_zero : Tendsto (f a) atBot (𝓝 0)
    - iInf_rat_gt_eq : forall t : Rat, ⨅ r : Ioi t, f a r = f a t

中文:
结构 是RatStieltjesPoint
  参数: (f : α -> 有理数 -> 实数) (a : α)
  公理与运算 (4 个):
    - mono : 递增 (f a)
    - tendsto_atTop_one : 收敛 (f a) atTop (𝓝 1)
    - tendsto_atBot_zero : 收敛 (f a) atBot (𝓝 0)
    - iInf_rat_gt_eq : 对任意 t : 有理数, ⨅ r : 左开右无界区间 t, f a r = f a t
-/
structure IsRatStieltjesPoint (f : α -> Rat -> Real) (a : α) : Prop where
  mono : Monotone (f a)
  tendsto_atTop_one : Tendsto (f a) atTop (𝓝 1)
  tendsto_atBot_zero : Tendsto (f a) atBot (𝓝 0)
  iInf_rat_gt_eq : forall t : Rat, ⨅ r : Ioi t, f a r = f a t

/--
lemma `isRatStieltjesPoint_unit_prod_iff` / 引理 `isRatStieltjesPoint_unit_prod_iff`

English:
lemma isRatStieltjesPoint_unit_prod_iff
  given: (f : α -> Rat -> Real) (a : α)
  proof: by
  constructor <;>
    exact fun h => ⟨h.mono, h.tendsto_atTop_one, h.tendsto_atBot_zero, h.iInf_rat_gt_eq⟩

中文:
引理 isRatStieltjesPoint_unit_prod_iff
  条件: (f : α -> 有理数 -> 实数) (a : α)
  证明: by
  constructor <;>
    exact fun h => ⟨h.mono, h.tendsto_atTop_one, h.tendsto_atBot_zero, h.iInf_rat_gt_eq⟩

Depends on / 依赖: h.iInf_rat_gt_eq, h.mono, h.tendsto_atBot_zero, h.tendsto_atTop_one, iInf_rat_gt_eq, tendsto_atBot_zero, tendsto_atTop_one
-/
lemma isRatStieltjesPoint_unit_prod_iff (f : α -> Rat -> Real) (a : α) :
    IsRatStieltjesPoint (fun p : Unit × α => f p.2) ((), a)
      ↔ IsRatStieltjesPoint f a := by
  constructor <;>
    exact fun h => ⟨h.mono, h.tendsto_atTop_one, h.tendsto_atBot_zero, h.iInf_rat_gt_eq⟩

/--
lemma `measurableSet_isRatStieltjesPoint` / 引理 `measurableSet_isRatStieltjesPoint`

English:
lemma measurableSet_isRatStieltjesPoint
  given: [MeasurableSpace α] (hf : Measurable f)
  proof: by
  have h1 : MeasurableSet {a | Monotone (f a)} := by
    change MeasurableSet {a | forall q r (_ : q <= r), f a q <= f a r}
    simp_rw [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun q => ?_)
    refine MeasurableSet.iInter (fun r => ?_)
    refine MeasurableSet.iInter (fun _ => ?_)
   

中文:
引理 measurableSet_isRatStieltjesPoint
  条件: [可测空间 α] (hf : 可测 f)
  证明: by
  have h1 : MeasurableSet {a | Monotone (f a)} := by
    change MeasurableSet {a | forall q r (_ : q <= r), f a q <= f a r}
    simp_rw [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun q => ?_)
    refine MeasurableSet.iInter (fun r => ?_)
    refine MeasurableSet.iInter (fun _ => ?_)
   

Depends on / 依赖: MeasurableSet, MeasurableSet.iInter, Monotone, Set.ofPred_forall, Tendsto, hf.eval, iInter, measurableSet_le, measurableSet_tendsto, ofPred_forall, simp_rw
-/
lemma measurableSet_isRatStieltjesPoint [MeasurableSpace α] (hf : Measurable f) :
    MeasurableSet {a | IsRatStieltjesPoint f a} := by
  have h1 : MeasurableSet {a | Monotone (f a)} := by
    change MeasurableSet {a | forall q r (_ : q <= r), f a q <= f a r}
    simp_rw [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun q => ?_)
    refine MeasurableSet.iInter (fun r => ?_)
    refine MeasurableSet.iInter (fun _ => ?_)
    exact measurableSet_le hf.eval hf.eval
  have h2 : MeasurableSet {a | Tendsto (f a) atTop (𝓝 1)} :=
    measurableSet_tendsto _ (fun q => hf.eval)
  have h3 : MeasurableSet {a | Tendsto (f a) atBot (𝓝 0)} :=
    measurableSet_tendsto _ (fun q => hf.eval)
  have h4 : MeasurableSet {a | forall t : Rat, ⨅ r : Ioi t, f a r = f a t} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun q => ?_)
    exact measurableSet_eq_fun (.iInf fun _ => hf.eval) hf.eval
  suffices {a | IsRatStieltjesPoint f a}
      = ({a | Monotone (f a)} inter {a | Tendsto (f a) atTop (𝓝 1)} inter {a | Tendsto (f a) atBot (𝓝 0)}
        inter {a | forall t : Rat, ⨅ r : Ioi t, f a r = f a t}) by
    rw [this]
    exact (((h1.inter h2).inter h3).inter h4)
  ext a
  simp only [mem_ofPred_eq, mem_inter_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨⟨⟨h.mono, h.tendsto_atTop_one⟩, h.tendsto_atBot_zero⟩, h.iInf_rat_gt_eq⟩
  · exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/--
lemma `IsRatStieltjesPoint.ite` / 引理 `IsRatStieltjesPoint.ite`

English:
lemma IsRatStieltjesPoint.ite
  statement: {f g : α -> Rat -> Real} {a : α} (p : α -> Prop) [DecidablePred p]
  proof: by split_ifs with h; exacts [(hf h).mono, (hg h).mono]
  tendsto_atTop_one := by
    split_ifs with h; exacts [(hf h).tendsto_atTop_one, (hg h).tendsto_atTop_one]
  tendsto_atBot_zero := by
    split_ifs with h; exacts [(hf h).tendsto_atBot_zero, (hg h).tendsto_atBot_zero]
  iInf_rat_gt_eq := by spl

中文:
引理 是RatStieltjesPoint.ite
  结论: {f g : α -> 有理数 -> 实数} {a : α} (p : α -> 命题) [DecidablePred p]
  证明: by split_ifs with h; exacts [(hf h).mono, (hg h).mono]
  tendsto_atTop_one := by
    split_ifs with h; exacts [(hf h).tendsto_atTop_one, (hg h).tendsto_atTop_one]
  tendsto_atBot_zero := by
    split_ifs with h; exacts [(hf h).tendsto_atBot_zero, (hg h).tendsto_atBot_zero]
  iInf_rat_gt_eq := by spl

Depends on / 依赖: exacts, iInf_rat_gt_eq, split_ifs, tendsto_atBot_zero, tendsto_atTop_one
-/
lemma IsRatStieltjesPoint.ite {f g : α -> Rat -> Real} {a : α} (p : α -> Prop) [DecidablePred p]
    (hf : p a -> IsRatStieltjesPoint f a) (hg : ¬ p a -> IsRatStieltjesPoint g a) :
    IsRatStieltjesPoint (fun a => if p a then f a else g a) a where
  mono := by split_ifs with h; exacts [(hf h).mono, (hg h).mono]
  tendsto_atTop_one := by
    split_ifs with h; exacts [(hf h).tendsto_atTop_one, (hg h).tendsto_atTop_one]
  tendsto_atBot_zero := by
    split_ifs with h; exacts [(hf h).tendsto_atBot_zero, (hg h).tendsto_atBot_zero]
  iInf_rat_gt_eq := by split_ifs with h; exacts [(hf h).iInf_rat_gt_eq, (hg h).iInf_rat_gt_eq]

variable [MeasurableSpace α]

/--
Definition of `IsMeasurableRatCDF` / `IsMeasurableRatCDF` 的定义

English:
structure IsMeasurableRatCDF
  parameters: (f : α -> Rat -> Real)
  axioms and operations (2):
    - isRatStieltjesPoint : forall a, IsRatStieltjesPoint f a
    - measurable : Measurable f

中文:
结构 是MeasurableRatCDF
  参数: (f : α -> 有理数 -> 实数)
  公理与运算 (2 个):
    - isRatStieltjesPoint : 对任意 a, 是RatStieltjesPoint f a
    - measurable : 可测 f
-/
structure IsMeasurableRatCDF (f : α -> Rat -> Real) : Prop where
  isRatStieltjesPoint : forall a, IsRatStieltjesPoint f a
  measurable : Measurable f

/--
lemma `IsMeasurableRatCDF.nonneg` / 引理 `IsMeasurableRatCDF.nonneg`

English:
lemma IsMeasurableRatCDF.nonneg
  given: {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α) (q : Rat)
  proof: Monotone.le_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atBot_zero q

中文:
引理 是MeasurableRatCDF.nonneg
  条件: {f : α -> 有理数 -> 实数} (hf : 是MeasurableRatCDF f) (a : α) (q : 有理数)
  证明: Monotone.le_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atBot_zero q

Depends on / 依赖: Monotone, Monotone.le_of_tendsto, hf.isRatStieltjesPoint, isRatStieltjesPoint, le_of_tendsto, tendsto_atBot_zero
-/
lemma IsMeasurableRatCDF.nonneg {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α) (q : Rat) :
    0 <= f a q :=
  Monotone.le_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atBot_zero q

/--
lemma `IsMeasurableRatCDF.le_one` / 引理 `IsMeasurableRatCDF.le_one`

English:
lemma IsMeasurableRatCDF.le_one
  given: {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α) (q : Rat)
  proof: Monotone.ge_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atTop_one q

中文:
引理 是MeasurableRatCDF.le_one
  条件: {f : α -> 有理数 -> 实数} (hf : 是MeasurableRatCDF f) (a : α) (q : 有理数)
  证明: Monotone.ge_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atTop_one q

Depends on / 依赖: Monotone, Monotone.ge_of_tendsto, ge_of_tendsto, hf.isRatStieltjesPoint, isRatStieltjesPoint, tendsto_atTop_one
-/
lemma IsMeasurableRatCDF.le_one {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α) (q : Rat) :
    f a q <= 1 :=
  Monotone.ge_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atTop_one q

/--
lemma `IsMeasurableRatCDF.tendsto_atTop_one` / 引理 `IsMeasurableRatCDF.tendsto_atTop_one`

English:
lemma IsMeasurableRatCDF.tendsto_atTop_one
  given: {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α)
  proof: (hf.isRatStieltjesPoint a).tendsto_atTop_one

中文:
引理 是MeasurableRatCDF.tendsto_atTop_one
  条件: {f : α -> 有理数 -> 实数} (hf : 是MeasurableRatCDF f) (a : α)
  证明: (hf.isRatStieltjesPoint a).tendsto_atTop_one

Depends on / 依赖: hf.isRatStieltjesPoint, isRatStieltjesPoint, tendsto_atTop_one
-/
lemma IsMeasurableRatCDF.tendsto_atTop_one {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α) :
    Tendsto (f a) atTop (𝓝 1) := (hf.isRatStieltjesPoint a).tendsto_atTop_one

/--
lemma `IsMeasurableRatCDF.tendsto_atBot_zero` / 引理 `IsMeasurableRatCDF.tendsto_atBot_zero`

English:
lemma IsMeasurableRatCDF.tendsto_atBot_zero
  given: {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α)
  proof: (hf.isRatStieltjesPoint a).tendsto_atBot_zero

中文:
引理 是MeasurableRatCDF.tendsto_atBot_zero
  条件: {f : α -> 有理数 -> 实数} (hf : 是MeasurableRatCDF f) (a : α)
  证明: (hf.isRatStieltjesPoint a).tendsto_atBot_zero

Depends on / 依赖: hf.isRatStieltjesPoint, isRatStieltjesPoint, tendsto_atBot_zero
-/
lemma IsMeasurableRatCDF.tendsto_atBot_zero {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α) :
    Tendsto (f a) atBot (𝓝 0) := (hf.isRatStieltjesPoint a).tendsto_atBot_zero

/--
lemma `IsMeasurableRatCDF.iInf_rat_gt_eq` / 引理 `IsMeasurableRatCDF.iInf_rat_gt_eq`

English:
lemma IsMeasurableRatCDF.iInf_rat_gt_eq
  statement: {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α)
  proof: (hf.isRatStieltjesPoint a).iInf_rat_gt_eq q

中文:
引理 是MeasurableRatCDF.iInf_rat_gt_eq
  结论: {f : α -> 有理数 -> 实数} (hf : 是MeasurableRatCDF f) (a : α)
  证明: (hf.isRatStieltjesPoint a).iInf_rat_gt_eq q

Depends on / 依赖: hf.isRatStieltjesPoint, iInf_rat_gt_eq, isRatStieltjesPoint
-/
lemma IsMeasurableRatCDF.iInf_rat_gt_eq {f : α -> Rat -> Real} (hf : IsMeasurableRatCDF f) (a : α)
    (q : Rat) :
    ⨅ r : Ioi q, f a r = f a q := (hf.isRatStieltjesPoint a).iInf_rat_gt_eq q

end IsMeasurableRatCDF

section DefaultRatCDF

/--
Definition of `defaultRatCDF` / `defaultRatCDF` 的定义

English:
definition defaultRatCDF
  signature: (q : Rat)
  body: if q < 0 then (0 : Real) else 1

中文:
定义 defaultRatCDF
  签名: (q : 有理数)
  定义体: if q < 0 then (0 : Real) else 1
-/
def defaultRatCDF (q : Rat) := if q < 0 then (0 : Real) else 1

/--
lemma `monotone_defaultRatCDF` / 引理 `monotone_defaultRatCDF`

English:
lemma monotone_defaultRatCDF
  statement: Monotone defaultRatCDF
  proof: by
  unfold defaultRatCDF
  intro x y hxy
  dsimp only
  split_ifs with h_1 h_2 h_2
  exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl]

中文:
引理 monotone_defaultRatCDF
  结论: 递增 defaultRatCDF
  证明: by
  unfold defaultRatCDF
  intro x y hxy
  dsimp only
  split_ifs with h_1 h_2 h_2
  exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl]

Depends on / 依赖: absurd, defaultRatCDF, exacts, hxy.trans_lt, le_rfl, split_ifs, trans_lt, zero_le_one
-/
lemma monotone_defaultRatCDF : Monotone defaultRatCDF := by
  unfold defaultRatCDF
  intro x y hxy
  dsimp only
  split_ifs with h_1 h_2 h_2
  exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl]

/--
lemma `defaultRatCDF_nonneg` / 引理 `defaultRatCDF_nonneg`

English:
lemma defaultRatCDF_nonneg
  given: (q : Rat)
  statement: 0 <= defaultRatCDF q
  proof: by
  unfold defaultRatCDF
  split_ifs
  exacts [le_rfl, zero_le_one]

中文:
引理 defaultRatCDF_nonneg
  条件: (q : 有理数)
  结论: 0 <= defaultRatCDF q
  证明: by
  unfold defaultRatCDF
  split_ifs
  exacts [le_rfl, zero_le_one]

Depends on / 依赖: defaultRatCDF, exacts, le_rfl, split_ifs, zero_le_one
-/
lemma defaultRatCDF_nonneg (q : Rat) : 0 <= defaultRatCDF q := by
  unfold defaultRatCDF
  split_ifs
  exacts [le_rfl, zero_le_one]

/--
lemma `defaultRatCDF_le_one` / 引理 `defaultRatCDF_le_one`

English:
lemma defaultRatCDF_le_one
  given: (q : Rat)
  statement: defaultRatCDF q <= 1
  proof: by
  unfold defaultRatCDF
  split_ifs <;> simp

中文:
引理 defaultRatCDF_le_one
  条件: (q : 有理数)
  结论: defaultRatCDF q <= 1
  证明: by
  unfold defaultRatCDF
  split_ifs <;> simp

Depends on / 依赖: defaultRatCDF, split_ifs
-/
lemma defaultRatCDF_le_one (q : Rat) : defaultRatCDF q <= 1 := by
  unfold defaultRatCDF
  split_ifs <;> simp

/--
lemma `tendsto_defaultRatCDF_atTop` / 引理 `tendsto_defaultRatCDF_atTop`

English:
lemma tendsto_defaultRatCDF_atTop
  statement: Tendsto defaultRatCDF atTop (𝓝 1)
  proof: by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq]; rw [eventually_atTop]
  exact ⟨0, fun q hq => (if_neg (not_lt.mpr hq)).symm⟩

中文:
引理 tendsto_defaultRatCDF_atTop
  结论: 收敛 defaultRatCDF atTop (𝓝 1)
  证明: by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq]; rw [eventually_atTop]
  exact ⟨0, fun q hq => (if_neg (not_lt.mpr hq)).symm⟩

Depends on / 依赖: EventuallyEq, eventually_atTop, if_neg, not_lt, not_lt.mpr, tendsto_congr, tendsto_const_nhds
-/
lemma tendsto_defaultRatCDF_atTop : Tendsto defaultRatCDF atTop (𝓝 1) := by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq]; rw [eventually_atTop]
  exact ⟨0, fun q hq => (if_neg (not_lt.mpr hq)).symm⟩

/--
lemma `tendsto_defaultRatCDF_atBot` / 引理 `tendsto_defaultRatCDF_atBot`

English:
lemma tendsto_defaultRatCDF_atBot
  statement: Tendsto defaultRatCDF atBot (𝓝 0)
  proof: by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq]; rw [eventually_atBot]
  refine ⟨-1, fun q hq => (if_pos (hq.trans_lt ?_)).symm⟩
  linarith

中文:
引理 tendsto_defaultRatCDF_atBot
  结论: 收敛 defaultRatCDF atBot (𝓝 0)
  证明: by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq]; rw [eventually_atBot]
  refine ⟨-1, fun q hq => (if_pos (hq.trans_lt ?_)).symm⟩
  linarith

Depends on / 依赖: EventuallyEq, eventually_atBot, hq.trans_lt, if_pos, tendsto_congr, tendsto_const_nhds, trans_lt
-/
lemma tendsto_defaultRatCDF_atBot : Tendsto defaultRatCDF atBot (𝓝 0) := by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq]; rw [eventually_atBot]
  refine ⟨-1, fun q hq => (if_pos (hq.trans_lt ?_)).symm⟩
  linarith

set_option backward.isDefEq.respectTransparency false in
/--
lemma `iInf_rat_gt_defaultRatCDF` / 引理 `iInf_rat_gt_defaultRatCDF`

English:
lemma iInf_rat_gt_defaultRatCDF
  given: (t : Rat)
  proof: by
  simp only [defaultRatCDF]
  have h_bdd : BddBelow (range fun r : ↥(Ioi t) => ite ((r : Rat) < 0) (0 : Real) 1) := by
    refine ⟨0, fun x hx => ?_⟩
    obtain ⟨y, rfl⟩ := mem_range.mpr hx
    dsimp only
    split_ifs
    exacts [le_rfl, zero_le_one]
  split_ifs with h
  · refine le_antisymm ?_ 

中文:
引理 iInf_rat_gt_defaultRatCDF
  条件: (t : 有理数)
  证明: by
  simp only [defaultRatCDF]
  have h_bdd : BddBelow (range fun r : ↥(Ioi t) => ite ((r : Rat) < 0) (0 : Real) 1) := by
    refine ⟨0, fun x hx => ?_⟩
    obtain ⟨y, rfl⟩ := mem_range.mpr hx
    dsimp only
    split_ifs
    exacts [le_rfl, zero_le_one]
  split_ifs with h
  · refine le_antisymm ?_ 

Depends on / 依赖: BddBelow, Subtype, Subtype.coe_mk, ciInf_le, coe_mk, defaultRatCDF, exacts, h_bdd, hq_neg, if_pos, le_antisymm, le_ciInf, le_rfl, mem_range, mem_range.mpr, split_ifs, zero_le_one
-/
lemma iInf_rat_gt_defaultRatCDF (t : Rat) :
    ⨅ r : Ioi t, defaultRatCDF r = defaultRatCDF t := by
  simp only [defaultRatCDF]
  have h_bdd : BddBelow (range fun r : ↥(Ioi t) => ite ((r : Rat) < 0) (0 : Real) 1) := by
    refine ⟨0, fun x hx => ?_⟩
    obtain ⟨y, rfl⟩ := mem_range.mpr hx
    dsimp only
    split_ifs
    exacts [le_rfl, zero_le_one]
  split_ifs with h
  · refine le_antisymm ?_ (le_ciInf fun x => ?_)
    · obtain ⟨q, htq, hq_neg⟩ : exists q, t < q ∧ q < 0 := ⟨t / 2, by linarith, by linarith⟩
      refine (ciInf_le h_bdd ⟨q, htq⟩).trans ?_
      rw [if_pos]
      rwa [Subtype.coe_mk]
    · split_ifs
      exacts [le_rfl, zero_le_one]
  · refine le_antisymm ?_ ?_
    · refine (ciInf_le h_bdd ⟨t + 1, lt_add_one t⟩).trans ?_
      split_ifs
      exacts [zero_le_one, le_rfl]
    · refine le_ciInf fun x => ?_
      rw [if_neg]
      rw [not_lt] at h ⊢
      exact h.trans (mem_Ioi.mp x.prop).le

/--
lemma `isRatStieltjesPoint_defaultRatCDF` / 引理 `isRatStieltjesPoint_defaultRatCDF`

English:
lemma isRatStieltjesPoint_defaultRatCDF
  given: (a : α)
  proof: monotone_defaultRatCDF
  tendsto_atTop_one := tendsto_defaultRatCDF_atTop
  tendsto_atBot_zero := tendsto_defaultRatCDF_atBot
  iInf_rat_gt_eq := iInf_rat_gt_defaultRatCDF

中文:
引理 isRatStieltjesPoint_defaultRatCDF
  条件: (a : α)
  证明: monotone_defaultRatCDF
  tendsto_atTop_one := tendsto_defaultRatCDF_atTop
  tendsto_atBot_zero := tendsto_defaultRatCDF_atBot
  iInf_rat_gt_eq := iInf_rat_gt_defaultRatCDF

Depends on / 依赖: monotone_defaultRatCDF
-/
lemma isRatStieltjesPoint_defaultRatCDF (a : α) :
    IsRatStieltjesPoint (fun (_ : α) => defaultRatCDF) a where
  mono := monotone_defaultRatCDF
  tendsto_atTop_one := tendsto_defaultRatCDF_atTop
  tendsto_atBot_zero := tendsto_defaultRatCDF_atBot
  iInf_rat_gt_eq := iInf_rat_gt_defaultRatCDF

/--
lemma `IsMeasurableRatCDF_defaultRatCDF` / 引理 `IsMeasurableRatCDF_defaultRatCDF`

English:
lemma IsMeasurableRatCDF_defaultRatCDF
  given: (α : Type*) [MeasurableSpace α]
  proof: isRatStieltjesPoint_defaultRatCDF
  measurable := measurable_const

中文:
引理 IsMeasurableRatCDF_defaultRatCDF
  条件: (α : 类型) [可测空间 α]
  证明: isRatStieltjesPoint_defaultRatCDF
  measurable := measurable_const

Depends on / 依赖: isRatStieltjesPoint_defaultRatCDF
-/
lemma IsMeasurableRatCDF_defaultRatCDF (α : Type*) [MeasurableSpace α] :
    IsMeasurableRatCDF (fun (_ : α) (q : Rat) => defaultRatCDF q) where
  isRatStieltjesPoint := isRatStieltjesPoint_defaultRatCDF
  measurable := measurable_const

end DefaultRatCDF

section ToRatCDF

variable {f : α -> Rat -> Real}

open scoped Classical in
/-- Turn a function `f : α → ℚ → ℝ` into another with the property `IsRatStieltjesPoint f a`
everywhere. At `a` that does not satisfy that property, `f a` is replaced by an arbitrary suitable
function.
Mainly useful when `f` satisfies the property `IsRatStieltjesPoint f a` almost everywhere with
respect to some measure. -/
noncomputable
/--
Definition of `toRatCDF` / `toRatCDF` 的定义

English:
definition toRatCDF
  signature: (f : α -> Rat -> Real)
  body: fun a =>
  if IsRatStieltjesPoint f a then f a else defaultRatCDF

中文:
定义 toRatCDF
  签名: (f : α -> 有理数 -> 实数)
  定义体: fun a =>
  if IsRatStieltjesPoint f a then f a else defaultRatCDF
-/
def toRatCDF (f : α -> Rat -> Real) : α -> Rat -> Real := fun a =>
  if IsRatStieltjesPoint f a then f a else defaultRatCDF

/--
lemma `toRatCDF_of_isRatStieltjesPoint` / 引理 `toRatCDF_of_isRatStieltjesPoint`

English:
lemma toRatCDF_of_isRatStieltjesPoint
  given: {a : α} (h : IsRatStieltjesPoint f a) (q : Rat)
  proof: by
  rw [toRatCDF]; rw [if_pos h]

中文:
引理 toRatCDF_of_isRatStieltjesPoint
  条件: {a : α} (h : 是RatStieltjesPoint f a) (q : 有理数)
  证明: by
  rw [toRatCDF]; rw [if_pos h]

Depends on / 依赖: if_pos, toRatCDF
-/
lemma toRatCDF_of_isRatStieltjesPoint {a : α} (h : IsRatStieltjesPoint f a) (q : Rat) :
    toRatCDF f a q = f a q := by
  rw [toRatCDF]; rw [if_pos h]

/--
lemma `toRatCDF_unit_prod` / 引理 `toRatCDF_unit_prod`

English:
lemma toRatCDF_unit_prod
  given: (a : α)
  proof: by
  unfold toRatCDF
  rw [isRatStieltjesPoint_unit_prod_iff]

中文:
引理 toRatCDF_unit_prod
  条件: (a : α)
  证明: by
  unfold toRatCDF
  rw [isRatStieltjesPoint_unit_prod_iff]

Depends on / 依赖: isRatStieltjesPoint_unit_prod_iff, toRatCDF
-/
lemma toRatCDF_unit_prod (a : α) :
    toRatCDF (fun (p : Unit × α) => f p.2) ((), a) = toRatCDF f a := by
  unfold toRatCDF
  rw [isRatStieltjesPoint_unit_prod_iff]

variable [MeasurableSpace α]

/--
lemma `measurable_toRatCDF` / 引理 `measurable_toRatCDF`

English:
lemma measurable_toRatCDF
  given: (hf : Measurable f)
  statement: Measurable (toRatCDF f)
  proof: Measurable.ite (measurableSet_isRatStieltjesPoint hf) hf measurable_const

中文:
引理 measurable_toRatCDF
  条件: (hf : 可测 f)
  结论: 可测 (toRatCDF f)
  证明: Measurable.ite (measurableSet_isRatStieltjesPoint hf) hf measurable_const

Depends on / 依赖: Measurable, Measurable.ite, measurableSet_isRatStieltjesPoint, measurable_const
-/
lemma measurable_toRatCDF (hf : Measurable f) : Measurable (toRatCDF f) :=
  Measurable.ite (measurableSet_isRatStieltjesPoint hf) hf measurable_const

/--
lemma `isMeasurableRatCDF_toRatCDF` / 引理 `isMeasurableRatCDF_toRatCDF`

English:
lemma isMeasurableRatCDF_toRatCDF
  given: (hf : Measurable f)
  proof: by
    classical
    exact IsRatStieltjesPoint.ite (IsRatStieltjesPoint f) id
      (fun _ => isRatStieltjesPoint_defaultRatCDF a)
  measurable := measurable_toRatCDF hf

中文:
引理 isMeasurableRatCDF_toRatCDF
  条件: (hf : 可测 f)
  证明: by
    classical
    exact IsRatStieltjesPoint.ite (IsRatStieltjesPoint f) id
      (fun _ => isRatStieltjesPoint_defaultRatCDF a)
  measurable := measurable_toRatCDF hf

Depends on / 依赖: IsRatStieltjesPoint, IsRatStieltjesPoint.ite, classical, isRatStieltjesPoint_defaultRatCDF, measurable, measurable_toRatCDF
-/
lemma isMeasurableRatCDF_toRatCDF (hf : Measurable f) :
    IsMeasurableRatCDF (toRatCDF f) where
  isRatStieltjesPoint a := by
    classical
    exact IsRatStieltjesPoint.ite (IsRatStieltjesPoint f) id
      (fun _ => isRatStieltjesPoint_defaultRatCDF a)
  measurable := measurable_toRatCDF hf

end ToRatCDF

section IsMeasurableRatCDF.stieltjesFunction

/-- Auxiliary definition for `IsMeasurableRatCDF.stieltjesFunction`: turn `f : α → ℚ → ℝ` into
a function `α → ℝ → ℝ` by assigning to `f a x` the infimum of `f a q` over `q : ℚ` with `x < q`. -/
noncomputable irreducible_def IsMeasurableRatCDF.stieltjesFunctionAux (f : α -> Rat -> Real) :
    α -> Real -> Real :=
  fun a x => ⨅ q : { q' : Rat // x < q' }, f a q

/--
lemma `IsMeasurableRatCDF.stieltjesFunctionAux_def'` / 引理 `IsMeasurableRatCDF.stieltjesFunctionAux_def'`

English:
lemma IsMeasurableRatCDF.stieltjesFunctionAux_def'
  given: (f : α -> Rat -> Real) (a : α)
  proof: by
  ext t; exact IsMeasurableRatCDF.stieltjesFunctionAux_def f a t

中文:
引理 是MeasurableRatCDF.stieltjesFunctionAux_def'
  条件: (f : α -> 有理数 -> 实数) (a : α)
  证明: by
  ext t; exact IsMeasurableRatCDF.stieltjesFunctionAux_def f a t

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunctionAux_def, stieltjesFunctionAux_def
-/
lemma IsMeasurableRatCDF.stieltjesFunctionAux_def' (f : α -> Rat -> Real) (a : α) :
    IsMeasurableRatCDF.stieltjesFunctionAux f a
      = fun (t : Real) => ⨅ r : { r' : Rat // t < r' }, f a r := by
  ext t; exact IsMeasurableRatCDF.stieltjesFunctionAux_def f a t

/--
lemma `IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod` / 引理 `IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod`

English:
lemma IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod
  given: {f : α -> Rat -> Real} (a : α)
  proof: by
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def']

中文:
引理 是MeasurableRatCDF.stieltjesFunctionAux_unit_prod
  条件: {f : α -> 有理数 -> 实数} (a : α)
  证明: by
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def']

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunctionAux_def, simp_rw, stieltjesFunctionAux_def
-/
lemma IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod {f : α -> Rat -> Real} (a : α) :
    IsMeasurableRatCDF.stieltjesFunctionAux (fun (p : Unit × α) => f p.2) ((), a)
      = IsMeasurableRatCDF.stieltjesFunctionAux f a := by
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def']

variable {f : α -> Rat -> Real} [MeasurableSpace α] (hf : IsMeasurableRatCDF f)
include hf

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsMeasurableRatCDF.stieltjesFunctionAux_eq` / 引理 `IsMeasurableRatCDF.stieltjesFunctionAux_eq`

English:
lemma IsMeasurableRatCDF.stieltjesFunctionAux_eq
  given: (a : α) (r : Rat)
  proof: by
  rw [← hf.iInf_rat_gt_eq a r]; rw [IsMeasurableRatCDF.stieltjesFunctionAux]
  refine Equiv.iInf_congr ?_ ?_
  · exact
      { toFun := fun t => ⟨t.1, mod_cast t.2⟩
        invFun := fun t => ⟨t.1, mod_cast t.2⟩
        left_inv := fun t => by simp only [Subtype.coe_eta]
        right_inv := fun 

中文:
引理 是MeasurableRatCDF.stieltjesFunctionAux_eq
  条件: (a : α) (r : 有理数)
  证明: by
  rw [← hf.iInf_rat_gt_eq a r]; rw [IsMeasurableRatCDF.stieltjesFunctionAux]
  refine Equiv.iInf_congr ?_ ?_
  · exact
      { toFun := fun t => ⟨t.1, mod_cast t.2⟩
        invFun := fun t => ⟨t.1, mod_cast t.2⟩
        left_inv := fun t => by simp only [Subtype.coe_eta]
        right_inv := fun 

Depends on / 依赖: Equiv.coe_fn_mk, Equiv.iInf_congr, IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunctionAux, Subtype, Subtype.coe_eta, Subtype.coe_mk, coe_eta, coe_fn_mk, coe_mk, hf.iInf_rat_gt_eq, iInf_congr, iInf_rat_gt_eq, invFun, left_inv, mod_cast, right_inv, stieltjesFunctionAux
-/
lemma IsMeasurableRatCDF.stieltjesFunctionAux_eq (a : α) (r : Rat) :
    IsMeasurableRatCDF.stieltjesFunctionAux f a r = f a r := by
  rw [← hf.iInf_rat_gt_eq a r]; rw [IsMeasurableRatCDF.stieltjesFunctionAux]
  refine Equiv.iInf_congr ?_ ?_
  · exact
      { toFun := fun t => ⟨t.1, mod_cast t.2⟩
        invFun := fun t => ⟨t.1, mod_cast t.2⟩
        left_inv := fun t => by simp only [Subtype.coe_eta]
        right_inv := fun t => by simp only [Subtype.coe_eta] }
  · intro t
    simp only [Equiv.coe_fn_mk, Subtype.coe_mk]

/--
lemma `IsMeasurableRatCDF.stieltjesFunctionAux_nonneg` / 引理 `IsMeasurableRatCDF.stieltjesFunctionAux_nonneg`

English:
lemma IsMeasurableRatCDF.stieltjesFunctionAux_nonneg
  given: (a : α) (r : Real)
  proof: by
  have : Nonempty { r' : Rat // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  exact le_ciInf fun r' => hf.nonneg a _

中文:
引理 是MeasurableRatCDF.stieltjesFunctionAux_nonneg
  条件: (a : α) (r : 实数)
  证明: by
  have : Nonempty { r' : Rat // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  exact le_ciInf fun r' => hf.nonneg a _

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunctionAux_def, Nonempty, exists_rat_gt, hf.nonneg, le_ciInf, nonneg, stieltjesFunctionAux_def
-/
lemma IsMeasurableRatCDF.stieltjesFunctionAux_nonneg (a : α) (r : Real) :
    0 <= IsMeasurableRatCDF.stieltjesFunctionAux f a r := by
  have : Nonempty { r' : Rat // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  exact le_ciInf fun r' => hf.nonneg a _

/--
lemma `IsMeasurableRatCDF.monotone_stieltjesFunctionAux` / 引理 `IsMeasurableRatCDF.monotone_stieltjesFunctionAux`

English:
lemma IsMeasurableRatCDF.monotone_stieltjesFunctionAux
  given: (a : α)
  proof: by
  intro x y hxy
  have : Nonempty { r' : Rat // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  refine le_ciInf fun r => (ciInf_le ?_ ?_).trans_eq ?_
  · refine ⟨0, fun z => ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg

中文:
引理 是MeasurableRatCDF.monotone_stieltjesFunctionAux
  条件: (a : α)
  证明: by
  intro x y hxy
  have : Nonempty { r' : Rat // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  refine le_ciInf fun r => (ciInf_le ?_ ?_).trans_eq ?_
  · refine ⟨0, fun z => ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunctionAux_def, Nonempty, ciInf_le, exists_rat_gt, hf.nonneg, hxy.trans_lt, le_ciInf, nonneg, r.prop, simp_rw, stieltjesFunctionAux_def, trans_eq, trans_lt
-/
lemma IsMeasurableRatCDF.monotone_stieltjesFunctionAux (a : α) :
    Monotone (IsMeasurableRatCDF.stieltjesFunctionAux f a) := by
  intro x y hxy
  have : Nonempty { r' : Rat // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  refine le_ciInf fun r => (ciInf_le ?_ ?_).trans_eq ?_
  · refine ⟨0, fun z => ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r.1, hxy.trans_lt r.prop⟩
  · rfl

/--
lemma `IsMeasurableRatCDF.continuousWithinAt_stieltjesFunctionAux_Ici` / 引理 `IsMeasurableRatCDF.continuousWithinAt_stieltjesFunctionAux_Ici`

English:
lemma IsMeasurableRatCDF.continuousWithinAt_stieltjesFunctionAux_Ici
  given: (a : α) (x : Real)
  proof: by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  convert! Monotone.tendsto_nhdsGT (monotone_stieltjesFunctionAux hf a) x
  rw [sInf_image']
  have h' : ⨅ r : Ioi x, stieltjesFunctionAux f a r
      = ⨅ r : { r' : Rat // x < r' }, stieltjesFunctionAux f a r := by
    refine Real.iInf_Ioi_eq_iInf_rat_gt x

中文:
引理 是MeasurableRatCDF.continuousWithinAt_stieltjesFunctionAux_Ici
  条件: (a : α) (x : 实数)
  证明: by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  convert! Monotone.tendsto_nhdsGT (monotone_stieltjesFunctionAux hf a) x
  rw [sInf_image']
  have h' : ⨅ r : Ioi x, stieltjesFunctionAux f a r
      = ⨅ r : { r' : Rat // x < r' }, stieltjesFunctionAux f a r := by
    refine Real.iInf_Ioi_eq_iInf_rat_gt x

Depends on / 依赖: Monotone, Monotone.tendsto_nhdsGT, Real.iInf_Ioi_eq_iInf_rat_gt, continuousWithinAt_Ioi_iff_Ici, convert, iInf_Ioi_eq_iInf_rat_gt, monotone_stieltjesFunctionAux, sInf_image, stieltjesFunctionAux, stieltjesFunctionAux_nonneg, tendsto_nhdsGT
-/
lemma IsMeasurableRatCDF.continuousWithinAt_stieltjesFunctionAux_Ici (a : α) (x : Real) :
    ContinuousWithinAt (IsMeasurableRatCDF.stieltjesFunctionAux f a) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  convert! Monotone.tendsto_nhdsGT (monotone_stieltjesFunctionAux hf a) x
  rw [sInf_image']
  have h' : ⨅ r : Ioi x, stieltjesFunctionAux f a r
      = ⨅ r : { r' : Rat // x < r' }, stieltjesFunctionAux f a r := by
    refine Real.iInf_Ioi_eq_iInf_rat_gt x ?_ (monotone_stieltjesFunctionAux hf a)
    refine ⟨0, fun z => ?_⟩
    rintro ⟨u, -, rfl⟩
    exact stieltjesFunctionAux_nonneg hf a u
  have h'' :
    ⨅ r : { r' : Rat // x < r' }, stieltjesFunctionAux f a r =
      ⨅ r : { r' : Rat // x < r' }, f a r := by
    congr with r
    exact stieltjesFunctionAux_eq hf a r
  rw [h']; rw [h'']; rw [ContinuousWithinAt]
  congr!
  rw [stieltjesFunctionAux_def]

/--
Definition of `IsMeasurableRatCDF.stieltjesFunction` / `IsMeasurableRatCDF.stieltjesFunction` 的定义

English:
definition IsMeasurableRatCDF.stieltjesFunction
  signature: (a : α)
  body: stieltjesFunctionAux f a
  mono' := monotone_stieltjesFunctionAux hf a
  right_continuous' x := continuousWithinAt_stieltjesFunctionAux_Ici hf a x

中文:
定义 是MeasurableRatCDF.stieltjesFunction
  签名: (a : α)
  定义体: stieltjesFunctionAux f a
  mono' := monotone_stieltjesFunctionAux hf a
  right_continuous' x := continuousWithinAt_stieltjesFunctionAux_Ici hf a x

Depends on / 依赖: stieltjesFunctionAux
-/
noncomputable def IsMeasurableRatCDF.stieltjesFunction (a : α) : StieltjesFunction Real where
  toFun := stieltjesFunctionAux f a
  mono' := monotone_stieltjesFunctionAux hf a
  right_continuous' x := continuousWithinAt_stieltjesFunctionAux_Ici hf a x

/--
lemma `IsMeasurableRatCDF.stieltjesFunction_eq` / 引理 `IsMeasurableRatCDF.stieltjesFunction_eq`

English:
lemma IsMeasurableRatCDF.stieltjesFunction_eq
  given: (a : α) (r : Rat)
  statement: hf.stieltjesFunction a r = f a r
  proof: stieltjesFunctionAux_eq hf a r

中文:
引理 是MeasurableRatCDF.stieltjesFunction_eq
  条件: (a : α) (r : 有理数)
  结论: hf.stieltjesFunction a r = f a r
  证明: stieltjesFunctionAux_eq hf a r

Depends on / 依赖: stieltjesFunctionAux_eq
-/
lemma IsMeasurableRatCDF.stieltjesFunction_eq (a : α) (r : Rat) : hf.stieltjesFunction a r = f a r :=
  stieltjesFunctionAux_eq hf a r

/--
lemma `IsMeasurableRatCDF.stieltjesFunction_nonneg` / 引理 `IsMeasurableRatCDF.stieltjesFunction_nonneg`

English:
lemma IsMeasurableRatCDF.stieltjesFunction_nonneg
  given: (a : α) (r : Real)
  statement: 0 <= hf.stieltjesFunction a r
  proof: stieltjesFunctionAux_nonneg hf a r

中文:
引理 是MeasurableRatCDF.stieltjesFunction_nonneg
  条件: (a : α) (r : 实数)
  结论: 0 <= hf.stieltjesFunction a r
  证明: stieltjesFunctionAux_nonneg hf a r

Depends on / 依赖: stieltjesFunctionAux_nonneg
-/
lemma IsMeasurableRatCDF.stieltjesFunction_nonneg (a : α) (r : Real) : 0 <= hf.stieltjesFunction a r :=
  stieltjesFunctionAux_nonneg hf a r

/--
lemma `IsMeasurableRatCDF.stieltjesFunction_le_one` / 引理 `IsMeasurableRatCDF.stieltjesFunction_le_one`

English:
lemma IsMeasurableRatCDF.stieltjesFunction_le_one
  given: (a : α) (x : Real)
  proof: by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  simp_rw [IsMeasurableRatCDF.stieltjesFunction_eq]
  refine ciInf_le_of_le ?_ ?_ (hf.le_one _ _)
  · refine ⟨0, fun z => ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r, hrx⟩

中文:
引理 是MeasurableRatCDF.stieltjesFunction_le_one
  条件: (a : α) (x : 实数)
  证明: by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  simp_rw [IsMeasurableRatCDF.stieltjesFunction_eq]
  refine ciInf_le_of_le ?_ ?_ (hf.le_one _ _)
  · refine ⟨0, fun z => ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r, hrx⟩

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunction_eq, StieltjesFunction, StieltjesFunction.iInf_rat_gt_eq, ciInf_le_of_le, exists_rat_gt, hf.le_one, hf.nonneg, iInf_rat_gt_eq, le_one, nonneg, simp_rw, stieltjesFunction_eq
-/
lemma IsMeasurableRatCDF.stieltjesFunction_le_one (a : α) (x : Real) :
    hf.stieltjesFunction a x <= 1 := by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  simp_rw [IsMeasurableRatCDF.stieltjesFunction_eq]
  refine ciInf_le_of_le ?_ ?_ (hf.le_one _ _)
  · refine ⟨0, fun z => ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r, hrx⟩

/--
lemma `IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot` / 引理 `IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot`

English:
lemma IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot
  given: (a : α)
  proof: by
  have h_exists : forall x : Real, exists q : Rat, x < q ∧ ↑q < x + 1 := fun x => exists_rat_btwn (lt_add_one x)
  let qs : Real -> Rat := fun x => (h_exists x).choose
  have hqs_tendsto : Tendsto qs atBot atBot := by
    rw [tendsto_atBot_atBot]
    refine fun q => ⟨q - 1, fun y hy => ?_⟩
    ha

中文:
引理 是MeasurableRatCDF.tendsto_stieltjesFunction_atBot
  条件: (a : α)
  证明: by
  have h_exists : forall x : Real, exists q : Rat, x < q ∧ ↑q < x + 1 := fun x => exists_rat_btwn (lt_add_one x)
  let qs : Real -> Rat := fun x => (h_exists x).choose
  have hqs_tendsto : Tendsto qs atBot atBot := by
    rw [tendsto_atBot_atBot]
    refine fun q => ⟨q - 1, fun y hy => ?_⟩
    ha

Depends on / 依赖: Tendsto, add_le_add, choose_spec, exists_rat_btwn, h_exists, h_le, hqs_tendsto, le.trans, le_rfl, lt_add_one, mod_cast, sub_add_cancel, tendsto_atBot_atBot, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le
-/
lemma IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot (a : α) :
    Tendsto (hf.stieltjesFunction a) atBot (𝓝 0) := by
  have h_exists : forall x : Real, exists q : Rat, x < q ∧ ↑q < x + 1 := fun x => exists_rat_btwn (lt_add_one x)
  let qs : Real -> Rat := fun x => (h_exists x).choose
  have hqs_tendsto : Tendsto qs atBot atBot := by
    rw [tendsto_atBot_atBot]
    refine fun q => ⟨q - 1, fun y hy => ?_⟩
    have h_le : ↑(qs y) <= (q : Real) - 1 + 1 :=
      (h_exists y).choose_spec.2.le.trans (add_le_add hy le_rfl)
    rw [sub_add_cancel] at h_le
    exact mod_cast h_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((hf.tendsto_atBot_zero a).comp hqs_tendsto) (stieltjesFunction_nonneg hf a) fun x => ?_
  rw [Function.comp_apply]; rw [← stieltjesFunction_eq hf]
  exact (hf.stieltjesFunction a).mono (h_exists x).choose_spec.1.le

/--
lemma `IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop` / 引理 `IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop`

English:
lemma IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop
  given: (a : α)
  proof: by
  have h_exists : forall x : Real, exists q : Rat, x - 1 < q ∧ ↑q < x := fun x => exists_rat_btwn (sub_one_lt x)
  let qs : Real -> Rat := fun x => (h_exists x).choose
  have hqs_tendsto : Tendsto qs atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine fun q => ⟨q + 1, fun y hy => ?_⟩
    ha

中文:
引理 是MeasurableRatCDF.tendsto_stieltjesFunction_atTop
  条件: (a : α)
  证明: by
  have h_exists : forall x : Real, exists q : Rat, x - 1 < q ∧ ↑q < x := fun x => exists_rat_btwn (sub_one_lt x)
  let qs : Real -> Rat := fun x => (h_exists x).choose
  have hqs_tendsto : Tendsto qs atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine fun q => ⟨q + 1, fun y hy => ?_⟩
    ha

Depends on / 依赖: Tendsto, choose_spec, exists_rat_btwn, h_exists, h_le, hf.tendsto_atTop_one, hqs_tendsto, hy.trans, le_of_add_le_add_right, sub_le_iff_le_add, sub_one_lt, tendsto_atTop_atTop, tendsto_atTop_one, tendsto_of_tendsto_of_tendsto_of_le_of_le
-/
lemma IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop (a : α) :
    Tendsto (hf.stieltjesFunction a) atTop (𝓝 1) := by
  have h_exists : forall x : Real, exists q : Rat, x - 1 < q ∧ ↑q < x := fun x => exists_rat_btwn (sub_one_lt x)
  let qs : Real -> Rat := fun x => (h_exists x).choose
  have hqs_tendsto : Tendsto qs atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine fun q => ⟨q + 1, fun y hy => ?_⟩
    have h_le : y - 1 <= qs y := (h_exists y).choose_spec.1.le
    rw [sub_le_iff_le_add] at h_le
    exact_mod_cast le_of_add_le_add_right (hy.trans h_le)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ((hf.tendsto_atTop_one a).comp hqs_tendsto)
      tendsto_const_nhds ?_ (stieltjesFunction_le_one hf a)
  intro x
  rw [Function.comp_apply]; rw [← stieltjesFunction_eq hf]
  exact (hf.stieltjesFunction a).mono (le_of_lt (h_exists x).choose_spec.2)

/--
lemma `IsMeasurableRatCDF.measurable_stieltjesFunction` / 引理 `IsMeasurableRatCDF.measurable_stieltjesFunction`

English:
lemma IsMeasurableRatCDF.measurable_stieltjesFunction
  given: (x : Real)
  proof: by
  have : (fun a => hf.stieltjesFunction a x) = fun a => ⨅ r : { r' : Rat // x < r' }, f a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [stieltjesFunction_eq]
  rw [this]
  exact .iInf (fun q => hf.measurable.eval)

中文:
引理 是MeasurableRatCDF.measurable_stieltjesFunction
  条件: (x : 实数)
  证明: by
  have : (fun a => hf.stieltjesFunction a x) = fun a => ⨅ r : { r' : Rat // x < r' }, f a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [stieltjesFunction_eq]
  rw [this]
  exact .iInf (fun q => hf.measurable.eval)

Depends on / 依赖: StieltjesFunction, StieltjesFunction.iInf_rat_gt_eq, hf.measurable.eval, hf.stieltjesFunction, iInf_rat_gt_eq, measurable, stieltjesFunction, stieltjesFunction_eq
-/
lemma IsMeasurableRatCDF.measurable_stieltjesFunction (x : Real) :
    Measurable fun a => hf.stieltjesFunction a x := by
  have : (fun a => hf.stieltjesFunction a x) = fun a => ⨅ r : { r' : Rat // x < r' }, f a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [stieltjesFunction_eq]
  rw [this]
  exact .iInf (fun q => hf.measurable.eval)

/--
lemma `IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction` / 引理 `IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction`

English:
lemma IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction
  given: (x : Real)
  proof: (measurable_stieltjesFunction hf x).stronglyMeasurable

中文:
引理 是MeasurableRatCDF.stronglyMeasurable_stieltjesFunction
  条件: (x : 实数)
  证明: (measurable_stieltjesFunction hf x).stronglyMeasurable

Depends on / 依赖: measurable_stieltjesFunction, stronglyMeasurable
-/
lemma IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction (x : Real) :
    StronglyMeasurable fun a => hf.stieltjesFunction a x :=
  (measurable_stieltjesFunction hf x).stronglyMeasurable

section Measure

/--
lemma `IsMeasurableRatCDF.measure_stieltjesFunction_Iic` / 引理 `IsMeasurableRatCDF.measure_stieltjesFunction_Iic`

English:
lemma IsMeasurableRatCDF.measure_stieltjesFunction_Iic
  given: (a : α) (x : Real)
  proof: by
  rw [← sub_zero (hf.stieltjesFunction a x)]
  exact (hf.stieltjesFunction a).measure_Iic (tendsto_stieltjesFunction_atBot hf a) _

中文:
引理 是MeasurableRatCDF.measure_stieltjesFunction_Iic
  条件: (a : α) (x : 实数)
  证明: by
  rw [← sub_zero (hf.stieltjesFunction a x)]
  exact (hf.stieltjesFunction a).measure_Iic (tendsto_stieltjesFunction_atBot hf a) _

Depends on / 依赖: hf.stieltjesFunction, measure_Iic, stieltjesFunction, sub_zero, tendsto_stieltjesFunction_atBot
-/
lemma IsMeasurableRatCDF.measure_stieltjesFunction_Iic (a : α) (x : Real) :
    (hf.stieltjesFunction a).measure (Iic x) = ENNReal.ofReal (hf.stieltjesFunction a x) := by
  rw [← sub_zero (hf.stieltjesFunction a x)]
  exact (hf.stieltjesFunction a).measure_Iic (tendsto_stieltjesFunction_atBot hf a) _

/--
lemma `IsMeasurableRatCDF.measure_stieltjesFunction_univ` / 引理 `IsMeasurableRatCDF.measure_stieltjesFunction_univ`

English:
lemma IsMeasurableRatCDF.measure_stieltjesFunction_univ
  given: (a : α)
  proof: by
  rw [← ENNReal.ofReal_one]; rw [← sub_zero (1 : Real)]
  exact StieltjesFunction.measure_univ _ (tendsto_stieltjesFunction_atBot hf a)
    (tendsto_stieltjesFunction_atTop hf a)

中文:
引理 是MeasurableRatCDF.measure_stieltjesFunction_univ
  条件: (a : α)
  证明: by
  rw [← ENNReal.ofReal_one]; rw [← sub_zero (1 : Real)]
  exact StieltjesFunction.measure_univ _ (tendsto_stieltjesFunction_atBot hf a)
    (tendsto_stieltjesFunction_atTop hf a)

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, StieltjesFunction, StieltjesFunction.measure_univ, measure_univ, ofReal_one, sub_zero, tendsto_stieltjesFunction_atBot, tendsto_stieltjesFunction_atTop
-/
lemma IsMeasurableRatCDF.measure_stieltjesFunction_univ (a : α) :
    (hf.stieltjesFunction a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one]; rw [← sub_zero (1 : Real)]
  exact StieltjesFunction.measure_univ _ (tendsto_stieltjesFunction_atBot hf a)
    (tendsto_stieltjesFunction_atTop hf a)

/--
Instance `IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction` / 实例 `IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction`

English:
instance IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction
  signature: (a : α)
  body: ⟨measure_stieltjesFunction_univ hf a⟩

中文:
实例 是MeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction
  签名: (a : α)
  定义体: ⟨measure_stieltjesFunction_univ hf a⟩

Depends on / 依赖: measure_stieltjesFunction_univ
-/
instance IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction (a : α) :
    IsProbabilityMeasure (hf.stieltjesFunction a).measure :=
  ⟨measure_stieltjesFunction_univ hf a⟩

/--
lemma `IsMeasurableRatCDF.measurable_measure_stieltjesFunction` / 引理 `IsMeasurableRatCDF.measurable_measure_stieltjesFunction`

English:
lemma IsMeasurableRatCDF.measurable_measure_stieltjesFunction
  proof: by
  apply_rules [StieltjesFunction.measurable_measure, measurable_stieltjesFunction,
    tendsto_stieltjesFunction_atBot, tendsto_stieltjesFunction_atTop]

中文:
引理 是MeasurableRatCDF.measurable_measure_stieltjesFunction
  证明: by
  apply_rules [StieltjesFunction.measurable_measure, measurable_stieltjesFunction,
    tendsto_stieltjesFunction_atBot, tendsto_stieltjesFunction_atTop]

Depends on / 依赖: StieltjesFunction, StieltjesFunction.measurable_measure, apply_rules, measurable_measure, measurable_stieltjesFunction, tendsto_stieltjesFunction_atBot, tendsto_stieltjesFunction_atTop
-/
lemma IsMeasurableRatCDF.measurable_measure_stieltjesFunction :
    Measurable fun a => (hf.stieltjesFunction a).measure := by
  apply_rules [StieltjesFunction.measurable_measure, measurable_stieltjesFunction,
    tendsto_stieltjesFunction_atBot, tendsto_stieltjesFunction_atTop]

end Measure

end IsMeasurableRatCDF.stieltjesFunction

section stieltjesOfMeasurableRat

variable {f : α -> Rat -> Real} [MeasurableSpace α]

/-- Turn a measurable function `f : α → ℚ → ℝ` into a measurable function `α → StieltjesFunction ℝ`.
Composition of `toRatCDF` and `IsMeasurableRatCDF.stieltjesFunction`. -/
noncomputable
/--
Definition of `stieltjesOfMeasurableRat` / `stieltjesOfMeasurableRat` 的定义

English:
definition stieltjesOfMeasurableRat
  signature: (f : α -> Rat -> Real) (hf : Measurable f)
  body: (isMeasurableRatCDF_toRatCDF hf).stieltjesFunction

中文:
定义 stieltjesOfMeasurableRat
  签名: (f : α -> 有理数 -> 实数) (hf : 可测 f)
  定义体: (isMeasurableRatCDF_toRatCDF hf).stieltjesFunction

Depends on / 依赖: isMeasurableRatCDF_toRatCDF, stieltjesFunction
-/
def stieltjesOfMeasurableRat (f : α -> Rat -> Real) (hf : Measurable f) : α -> StieltjesFunction Real :=
  (isMeasurableRatCDF_toRatCDF hf).stieltjesFunction

/--
lemma `stieltjesOfMeasurableRat_eq` / 引理 `stieltjesOfMeasurableRat_eq`

English:
lemma stieltjesOfMeasurableRat_eq
  given: (hf : Measurable f) (a : α) (r : Rat)
  proof: IsMeasurableRatCDF.stieltjesFunction_eq _ a r

中文:
引理 stieltjesOfMeasurableRat_eq
  条件: (hf : 可测 f) (a : α) (r : 有理数)
  证明: IsMeasurableRatCDF.stieltjesFunction_eq _ a r

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunction_eq, stieltjesFunction_eq
-/
lemma stieltjesOfMeasurableRat_eq (hf : Measurable f) (a : α) (r : Rat) :
    stieltjesOfMeasurableRat f hf a r = toRatCDF f a r :=
  IsMeasurableRatCDF.stieltjesFunction_eq _ a r

/--
lemma `stieltjesOfMeasurableRat_unit_prod` / 引理 `stieltjesOfMeasurableRat_unit_prod`

English:
lemma stieltjesOfMeasurableRat_unit_prod
  given: (hf : Measurable f) (a : α)
  proof: by
  simp_rw [stieltjesOfMeasurableRat, IsMeasurableRatCDF.stieltjesFunction,
    ← IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod a]
  congr 1 with x
  congr 1 with p : 1
  cases p with
  | mk _ b => rw [← toRatCDF_unit_prod b]

中文:
引理 stieltjesOfMeasurableRat_unit_prod
  条件: (hf : 可测 f) (a : α)
  证明: by
  simp_rw [stieltjesOfMeasurableRat, IsMeasurableRatCDF.stieltjesFunction,
    ← IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod a]
  congr 1 with x
  congr 1 with p : 1
  cases p with
  | mk _ b => rw [← toRatCDF_unit_prod b]

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunction, IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod, simp_rw, stieltjesFunction, stieltjesFunctionAux_unit_prod, stieltjesOfMeasurableRat, toRatCDF_unit_prod
-/
lemma stieltjesOfMeasurableRat_unit_prod (hf : Measurable f) (a : α) :
    stieltjesOfMeasurableRat (fun (p : Unit × α) => f p.2) (hf.comp measurable_snd) ((), a)
      = stieltjesOfMeasurableRat f hf a := by
  simp_rw [stieltjesOfMeasurableRat, IsMeasurableRatCDF.stieltjesFunction,
    ← IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod a]
  congr 1 with x
  congr 1 with p : 1
  cases p with
  | mk _ b => rw [← toRatCDF_unit_prod b]

/--
lemma `stieltjesOfMeasurableRat_nonneg` / 引理 `stieltjesOfMeasurableRat_nonneg`

English:
lemma stieltjesOfMeasurableRat_nonneg
  given: (hf : Measurable f) (a : α) (r : Real)
  proof: IsMeasurableRatCDF.stieltjesFunction_nonneg _ a r

中文:
引理 stieltjesOfMeasurableRat_nonneg
  条件: (hf : 可测 f) (a : α) (r : 实数)
  证明: IsMeasurableRatCDF.stieltjesFunction_nonneg _ a r

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunction_nonneg, stieltjesFunction_nonneg
-/
lemma stieltjesOfMeasurableRat_nonneg (hf : Measurable f) (a : α) (r : Real) :
    0 <= stieltjesOfMeasurableRat f hf a r := IsMeasurableRatCDF.stieltjesFunction_nonneg _ a r

/--
lemma `stieltjesOfMeasurableRat_le_one` / 引理 `stieltjesOfMeasurableRat_le_one`

English:
lemma stieltjesOfMeasurableRat_le_one
  given: (hf : Measurable f) (a : α) (x : Real)
  proof: IsMeasurableRatCDF.stieltjesFunction_le_one _ a x

中文:
引理 stieltjesOfMeasurableRat_le_one
  条件: (hf : 可测 f) (a : α) (x : 实数)
  证明: IsMeasurableRatCDF.stieltjesFunction_le_one _ a x

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stieltjesFunction_le_one, stieltjesFunction_le_one
-/
lemma stieltjesOfMeasurableRat_le_one (hf : Measurable f) (a : α) (x : Real) :
    stieltjesOfMeasurableRat f hf a x <= 1 := IsMeasurableRatCDF.stieltjesFunction_le_one _ a x

/--
lemma `tendsto_stieltjesOfMeasurableRat_atBot` / 引理 `tendsto_stieltjesOfMeasurableRat_atBot`

English:
lemma tendsto_stieltjesOfMeasurableRat_atBot
  given: (hf : Measurable f) (a : α)
  proof: IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot _ a

中文:
引理 tendsto_stieltjesOfMeasurableRat_atBot
  条件: (hf : 可测 f) (a : α)
  证明: IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot _ a

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot, tendsto_stieltjesFunction_atBot
-/
lemma tendsto_stieltjesOfMeasurableRat_atBot (hf : Measurable f) (a : α) :
    Tendsto (stieltjesOfMeasurableRat f hf a) atBot (𝓝 0) :=
  IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot _ a

/--
lemma `tendsto_stieltjesOfMeasurableRat_atTop` / 引理 `tendsto_stieltjesOfMeasurableRat_atTop`

English:
lemma tendsto_stieltjesOfMeasurableRat_atTop
  given: (hf : Measurable f) (a : α)
  proof: IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop _ a

中文:
引理 tendsto_stieltjesOfMeasurableRat_atTop
  条件: (hf : 可测 f) (a : α)
  证明: IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop _ a

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop, tendsto_stieltjesFunction_atTop
-/
lemma tendsto_stieltjesOfMeasurableRat_atTop (hf : Measurable f) (a : α) :
    Tendsto (stieltjesOfMeasurableRat f hf a) atTop (𝓝 1) :=
  IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop _ a

/--
lemma `measurable_stieltjesOfMeasurableRat` / 引理 `measurable_stieltjesOfMeasurableRat`

English:
lemma measurable_stieltjesOfMeasurableRat
  given: (hf : Measurable f) (x : Real)
  proof: IsMeasurableRatCDF.measurable_stieltjesFunction _ x

中文:
引理 measurable_stieltjesOfMeasurableRat
  条件: (hf : 可测 f) (x : 实数)
  证明: IsMeasurableRatCDF.measurable_stieltjesFunction _ x

Depends on / 依赖: AtPrime, IsDedekindDomain, IsField, IsField.toField, IsLocalization, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain, IsMeasurableRatCDF, IsMeasurableRatCDF.measurable_stieltjesFunction, IsRegularRing, Localization, Localization.AtPrime, Localization.AtPrime.map_eq_maximalIdeal, infer_instance, isDiscreteValuationRing_of_dedekind_domain, isField_iff_maximalIdeal_eq, isRegularRing_iff, map_eq_maximalIdeal, measurable_stieltjesFunction, toField
-/
lemma measurable_stieltjesOfMeasurableRat (hf : Measurable f) (x : Real) :
    Measurable fun a => stieltjesOfMeasurableRat f hf a x :=
  IsMeasurableRatCDF.measurable_stieltjesFunction _ x

/--
lemma `stronglyMeasurable_stieltjesOfMeasurableRat` / 引理 `stronglyMeasurable_stieltjesOfMeasurableRat`

English:
lemma stronglyMeasurable_stieltjesOfMeasurableRat
  given: (hf : Measurable f) (x : Real)
  proof: IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction _ x

中文:
引理 stronglyMeasurable_stieltjesOfMeasurableRat
  条件: (hf : 可测 f) (x : 实数)
  证明: IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction _ x

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction, stronglyMeasurable_stieltjesFunction
-/
lemma stronglyMeasurable_stieltjesOfMeasurableRat (hf : Measurable f) (x : Real) :
    StronglyMeasurable fun a => stieltjesOfMeasurableRat f hf a x :=
  IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction _ x

section Measure

/--
lemma `measure_stieltjesOfMeasurableRat_Iic` / 引理 `measure_stieltjesOfMeasurableRat_Iic`

English:
lemma measure_stieltjesOfMeasurableRat_Iic
  given: (hf : Measurable f) (a : α) (x : Real)
  proof: IsMeasurableRatCDF.measure_stieltjesFunction_Iic _ _ _

中文:
引理 measure_stieltjesOfMeasurableRat_Iic
  条件: (hf : 可测 f) (a : α) (x : 实数)
  证明: IsMeasurableRatCDF.measure_stieltjesFunction_Iic _ _ _

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.measure_stieltjesFunction_Iic, measure_stieltjesFunction_Iic
-/
lemma measure_stieltjesOfMeasurableRat_Iic (hf : Measurable f) (a : α) (x : Real) :
    (stieltjesOfMeasurableRat f hf a).measure (Iic x)
      = ENNReal.ofReal (stieltjesOfMeasurableRat f hf a x) :=
  IsMeasurableRatCDF.measure_stieltjesFunction_Iic _ _ _

/--
lemma `measure_stieltjesOfMeasurableRat_univ` / 引理 `measure_stieltjesOfMeasurableRat_univ`

English:
lemma measure_stieltjesOfMeasurableRat_univ
  given: (hf : Measurable f) (a : α)
  proof: IsMeasurableRatCDF.measure_stieltjesFunction_univ _ _

中文:
引理 measure_stieltjesOfMeasurableRat_univ
  条件: (hf : 可测 f) (a : α)
  证明: IsMeasurableRatCDF.measure_stieltjesFunction_univ _ _

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.measure_stieltjesFunction_univ, measure_stieltjesFunction_univ
-/
lemma measure_stieltjesOfMeasurableRat_univ (hf : Measurable f) (a : α) :
    (stieltjesOfMeasurableRat f hf a).measure univ = 1 :=
  IsMeasurableRatCDF.measure_stieltjesFunction_univ _ _

/--
Instance `instIsProbabilityMeasure_stieltjesOfMeasurableRat` / 实例 `instIsProbabilityMeasure_stieltjesOfMeasurableRat`

English:
instance instIsProbabilityMeasure_stieltjesOfMeasurableRat
  body: IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction _ _

中文:
实例 instIsProbabilityMeasure_stieltjesOfMeasurableRat
  定义体: IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction _ _

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction, instIsProbabilityMeasure_stieltjesFunction
-/
instance instIsProbabilityMeasure_stieltjesOfMeasurableRat
    (hf : Measurable f) (a : α) :
    IsProbabilityMeasure (stieltjesOfMeasurableRat f hf a).measure :=
  IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction _ _

/--
lemma `measurable_measure_stieltjesOfMeasurableRat` / 引理 `measurable_measure_stieltjesOfMeasurableRat`

English:
lemma measurable_measure_stieltjesOfMeasurableRat
  given: (hf : Measurable f)
  proof: IsMeasurableRatCDF.measurable_measure_stieltjesFunction _

中文:
引理 measurable_measure_stieltjesOfMeasurableRat
  条件: (hf : 可测 f)
  证明: IsMeasurableRatCDF.measurable_measure_stieltjesFunction _

Depends on / 依赖: IsMeasurableRatCDF, IsMeasurableRatCDF.measurable_measure_stieltjesFunction, measurable_measure_stieltjesFunction
-/
lemma measurable_measure_stieltjesOfMeasurableRat (hf : Measurable f) :
    Measurable fun a => (stieltjesOfMeasurableRat f hf a).measure :=
  IsMeasurableRatCDF.measurable_measure_stieltjesFunction _

end Measure

end stieltjesOfMeasurableRat

end ProbabilityTheory
