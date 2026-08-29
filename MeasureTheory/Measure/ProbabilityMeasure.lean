/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Probability measures

This file defines the type of probability measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of probability measures is equipped with the topology of convergence
in distribution (weak convergence of measures). The topology of convergence in distribution is the
coarsest topology w.r.t. which for every bounded continuous `ℝ≥0`-valued random variable `X`, the
expected value of `X` depends continuously on the choice of probability measure. This is a special
case of the topology of weak convergence of finite measures.

## Main definitions

The main definitions are
* the type `MeasureTheory.ProbabilityMeasure Ω` with the topology of convergence in
  distribution (a.k.a. convergence in law, weak convergence of measures);
* `MeasureTheory.ProbabilityMeasure.toFiniteMeasure`: Interpret a probability measure as
  a finite measure;
* `MeasureTheory.FiniteMeasure.normalize`: Normalize a finite measure to a probability measure
  (returns junk for the zero measure).
* `MeasureTheory.ProbabilityMeasure.map`: The push-forward `f* μ` of a probability measure
  `μ` on `Ω` along a measurable function `f : Ω → Ω'`.

## Main results

* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`: Convergence of
  probability measures is characterized by the convergence of expected values of all bounded
  continuous random variables. This shows that the chosen definition of topology coincides with
  the common textbook definition of convergence in distribution, i.e., weak convergence of
  measures. A similar characterization by the convergence of expected values (in the
  `MeasureTheory.lintegral` sense) of all bounded continuous nonnegative random variables is
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`.
* `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto`: The convergence of finite
  measures to a nonzero limit is characterized by the convergence of the probability-normalized
  versions and of the total masses.
* `MeasureTheory.ProbabilityMeasure.continuous_map`: For a continuous function `f : Ω → Ω'`, the
  push-forward of probability measures `f* : ProbabilityMeasure Ω → ProbabilityMeasure Ω'` is
  continuous.
* `MeasureTheory.ProbabilityMeasure.t2Space`: The topology of convergence in distribution is
  Hausdorff on Borel spaces where indicators of closed sets have continuous decreasing
  approximating sequences (in particular on any pseudo-metrizable spaces).

TODO:
* Probability measures form a convex space.

## Implementation notes

The topology of convergence in distribution on `MeasureTheory.ProbabilityMeasure Ω` is inherited
weak convergence of finite measures via the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.

Like `MeasureTheory.FiniteMeasure Ω`, the implementation of `MeasureTheory.ProbabilityMeasure Ω`
is directly as a subtype of `MeasureTheory.Measure Ω`, and the coercion to a function is the
composition `ENNReal.toNNReal` and the coercion to function of `MeasureTheory.Measure Ω`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

convergence in distribution, convergence in law, weak convergence of measures, probability measure

-/

@[expose] public section


noncomputable section

open Set Filter BoundedContinuousFunction Topology
open scoped ENNReal NNReal

namespace MeasureTheory

section ProbabilityMeasure

/-! ### Probability measures

In this section we define the type of probability measures on a measurable space `Ω`, denoted by
`MeasureTheory.ProbabilityMeasure Ω`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[OpensMeasurableSpace Ω]`), then `MeasureTheory.ProbabilityMeasure Ω` is
equipped with the topology of weak convergence of measures. Since every probability measure is a
finite measure, this is implemented as the induced topology from the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.
-/


/--
Definition of `ProbabilityMeasure` / `ProbabilityMeasure` 的定义

English:
definition ProbabilityMeasure
  signature: (Ω : Type*) [MeasurableSpace Ω]
  body: { μ : Measure Ω // IsProbabilityMeasure μ }

中文:
定义 ProbabilityMeasure
  签名: (Ω : 类型) [MeasurableSpace Ω]
  定义体: { μ : Measure Ω // IsProbabilityMeasure μ }

Depends on / 依赖: IsProbabilityMeasure, Measure
-/
def ProbabilityMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsProbabilityMeasure μ }

namespace ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: Ω] : Inhabited (ProbabilityMeasure Ω)
  body: ⟨⟨Measure.dirac default, Measure.dirac.isProbabilityMeasure⟩⟩

中文:
实例 [Inhabited
  签名: Ω] : Inhabited (ProbabilityMeasure Ω)
  定义体: ⟨⟨Measure.dirac default, Measure.dirac.isProbabilityMeasure⟩⟩

Depends on / 依赖: Measure, Measure.dirac, Measure.dirac.isProbabilityMeasure, isProbabilityMeasure
-/
instance [Inhabited Ω] : Inhabited (ProbabilityMeasure Ω) :=
  ⟨⟨Measure.dirac default, Measure.dirac.isProbabilityMeasure⟩⟩

/-- Coercion from `MeasureTheory.ProbabilityMeasure Ω` to `MeasureTheory.Measure Ω`. -/
@[coe]
/--
Definition of `toMeasure` / `toMeasure` 的定义

English:
definition toMeasure
  signature: : ProbabilityMeasure Ω -> Measure Ω
  body: Subtype.val

中文:
定义 toMeasure
  签名: : ProbabilityMeasure Ω -> Measure Ω
  定义体: Subtype.val

Depends on / 依赖: Subtype, Subtype.val
-/
def toMeasure : ProbabilityMeasure Ω -> Measure Ω := Subtype.val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (ProbabilityMeasure Ω) (MeasureTheory.Measure Ω)
  body: { coe := toMeasure }

中文:
实例 :
  签名: Coe (ProbabilityMeasure Ω) (MeasureTheory.Measure Ω)
  定义体: { coe := toMeasure }

Depends on / 依赖: toMeasure
-/
instance : Coe (ProbabilityMeasure Ω) (MeasureTheory.Measure Ω) := { coe := toMeasure }

instance (μ : ProbabilityMeasure Ω) : IsProbabilityMeasure (μ : Measure Ω) :=
  μ.prop

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (μ : Measure Ω) (hμ)
  statement: toMeasure ⟨μ, hμ⟩ = μ
  proof: rfl

@[simp]

中文:
引理 coe_mk
  条件: (μ : Measure Ω) (hμ)
  结论: toMeasure ⟨μ, hμ⟩ = μ
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma coe_mk (μ : Measure Ω) (hμ) : toMeasure ⟨μ, hμ⟩ = μ := rfl

@[simp]
/--
theorem `val_eq_to_measure` / 定理 `val_eq_to_measure`

English:
theorem val_eq_to_measure
  given: (ν : ProbabilityMeasure Ω)
  statement: ν.val = (ν : Measure Ω)
  proof: rfl

中文:
定理 val_eq_to_measure
  条件: (ν : ProbabilityMeasure Ω)
  结论: ν.val = (ν : Measure Ω)
  证明: rfl
-/
theorem val_eq_to_measure (ν : ProbabilityMeasure Ω) : ν.val = (ν : Measure Ω) := rfl

/--
theorem `toMeasure_injective` / 定理 `toMeasure_injective`

English:
theorem toMeasure_injective
  statement: Function.Injective ((↑) : ProbabilityMeasure Ω -> Measure Ω)
  proof: Subtype.coe_injective

中文:
定理 toMeasure_injective
  结论: Function.Injective ((↑) : ProbabilityMeasure Ω -> Measure Ω)
  证明: Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem toMeasure_injective : Function.Injective ((↑) : ProbabilityMeasure Ω -> Measure Ω) :=
  Subtype.coe_injective

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (ProbabilityMeasure Ω) (Set Ω) Real>=0 where
  body: ((μ : Measure Ω) s).toNNReal
coe_injective μ ν h := toMeasure_injective Measure.ext fun s _ => by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s

中文:
实例 instFunLike
  签名: : FunLike (ProbabilityMeasure Ω) (Set Ω) 实数>=0 where
  定义体: ((μ : Measure Ω) s).toNNReal
coe_injective μ ν h := toMeasure_injective Measure.ext fun s _ => by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s

Depends on / 依赖: Measure, toNNReal
-/
instance instFunLike : FunLike (ProbabilityMeasure Ω) (Set Ω) Real>=0 where
  coe μ s := ((μ : Measure Ω) s).toNNReal
coe_injective μ ν h := toMeasure_injective Measure.ext fun s _ => by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s

/--
lemma `coeFn_def` / 引理 `coeFn_def`

English:
lemma coeFn_def
  given: (μ : ProbabilityMeasure Ω)
  statement: μ = fun s => ((μ : Measure Ω) s).toNNReal
  proof: rfl

中文:
引理 coeFn_def
  条件: (μ : ProbabilityMeasure Ω)
  结论: μ = fun s => ((μ : Measure Ω) s).toNN实数
  证明: rfl
-/
lemma coeFn_def (μ : ProbabilityMeasure Ω) : μ = fun s => ((μ : Measure Ω) s).toNNReal := rfl

/--
lemma `coeFn_mk` / 引理 `coeFn_mk`

English:
lemma coeFn_mk
  given: (μ : Measure Ω) (hμ)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coeFn_mk
  条件: (μ : Measure Ω) (hμ)
  证明: rfl

@[simp, norm_cast]

Depends on / 依赖: ProbabilityMeasure, toNNReal
-/
lemma coeFn_mk (μ : Measure Ω) (hμ) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ = fun s => (μ s).toNNReal := rfl

@[simp, norm_cast]
/--
lemma `mk_apply` / 引理 `mk_apply`

English:
lemma mk_apply
  given: (μ : Measure Ω) (hμ) (s : Set Ω)
  proof: rfl

@[simp, norm_cast]

中文:
引理 mk_apply
  条件: (μ : Measure Ω) (hμ) (s : Set Ω)
  证明: rfl

@[simp, norm_cast]

Depends on / 依赖: ProbabilityMeasure, toNNReal
-/
lemma mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ s = (μ s).toNNReal := rfl

@[simp, norm_cast]
/--
theorem `coeFn_univ` / 定理 `coeFn_univ`

English:
theorem coeFn_univ
  given: (ν : ProbabilityMeasure Ω)
  statement: ν univ = 1
  proof: congr_arg ENNReal.toNNReal ν.prop.measure_univ

@[simp]

中文:
定理 coeFn_univ
  条件: (ν : ProbabilityMeasure Ω)
  结论: ν univ = 1
  证明: congr_arg ENNReal.toNNReal ν.prop.measure_univ

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toNNReal, congr_arg, measure_univ, prop.measure_univ, toNNReal
-/
theorem coeFn_univ (ν : ProbabilityMeasure Ω) : ν univ = 1 :=
  congr_arg ENNReal.toNNReal ν.prop.measure_univ

@[simp]
/--
theorem `coeFn_empty` / 定理 `coeFn_empty`

English:
theorem coeFn_empty
  given: (ν : ProbabilityMeasure Ω)
  statement: ν ∅ = 0
  proof: by simp [coeFn_def]

中文:
定理 coeFn_empty
  条件: (ν : ProbabilityMeasure Ω)
  结论: ν ∅ = 0
  证明: by simp [coeFn_def]

Depends on / 依赖: coeFn_def
-/
theorem coeFn_empty (ν : ProbabilityMeasure Ω) : ν ∅ = 0 := by simp [coeFn_def]

/--
theorem `coeFn_univ_ne_zero` / 定理 `coeFn_univ_ne_zero`

English:
theorem coeFn_univ_ne_zero
  given: (ν : ProbabilityMeasure Ω)
  statement: ν univ != 0
  proof: by
  simp only [coeFn_univ, Ne, one_ne_zero, not_false_iff]

中文:
定理 coeFn_univ_ne_zero
  条件: (ν : ProbabilityMeasure Ω)
  结论: ν univ != 0
  证明: by
  simp only [coeFn_univ, Ne, one_ne_zero, not_false_iff]

Depends on / 依赖: coeFn_univ, not_false_iff, one_ne_zero
-/
theorem coeFn_univ_ne_zero (ν : ProbabilityMeasure Ω) : ν univ != 0 := by
  simp only [coeFn_univ, Ne, one_ne_zero, not_false_iff]

/--
theorem `measureReal_eq_coe_coeFn` / 定理 `measureReal_eq_coe_coeFn`

English:
theorem measureReal_eq_coe_coeFn
  given: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  proof: by
  simp [coeFn_def, Measure.real, ENNReal.toReal]

中文:
定理 measureReal_eq_coe_coeFn
  条件: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  证明: by
  simp [coeFn_def, Measure.real, ENNReal.toReal]
-/
@[simp] theorem measureReal_eq_coe_coeFn (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    (ν : Measure Ω).real s = ν s := by
  simp [coeFn_def, Measure.real, ENNReal.toReal]

/--
theorem `toNNReal_measureReal_eq_coeFn` / 定理 `toNNReal_measureReal_eq_coeFn`

English:
theorem toNNReal_measureReal_eq_coeFn
  given: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  proof: by
  simp

中文:
定理 toNNReal_measureReal_eq_coeFn
  条件: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  证明: by
  simp
-/
theorem toNNReal_measureReal_eq_coeFn (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ((ν : Measure Ω).real s).toNNReal = ν s := by
  simp

/--
Definition of `toFiniteMeasure` / `toFiniteMeasure` 的定义

English:
definition toFiniteMeasure
  signature: (μ : ProbabilityMeasure Ω)
  body: ⟨μ, inferInstance⟩

中文:
定义 toFiniteMeasure
  签名: (μ : ProbabilityMeasure Ω)
  定义体: ⟨μ, inferInstance⟩
-/
def toFiniteMeasure (μ : ProbabilityMeasure Ω) : FiniteMeasure Ω := ⟨μ, inferInstance⟩

/--
lemma `coeFn_toFiniteMeasure` / 引理 `coeFn_toFiniteMeasure`

English:
lemma coeFn_toFiniteMeasure
  given: (μ : ProbabilityMeasure Ω)
  statement: ⇑μ.toFiniteMeasure = μ
  proof: rfl

中文:
引理 coeFn_toFiniteMeasure
  条件: (μ : ProbabilityMeasure Ω)
  结论: ⇑μ.toFiniteMeasure = μ
  证明: rfl
-/
@[simp] lemma coeFn_toFiniteMeasure (μ : ProbabilityMeasure Ω) : ⇑μ.toFiniteMeasure = μ := rfl
/--
lemma `toFiniteMeasure_apply` / 引理 `toFiniteMeasure_apply`

English:
lemma toFiniteMeasure_apply
  given: (μ : ProbabilityMeasure Ω) (s : Set Ω)
  proof: rfl

@[simp]

中文:
引理 toFiniteMeasure_apply
  条件: (μ : ProbabilityMeasure Ω) (s : Set Ω)
  证明: rfl

@[simp]
-/
lemma toFiniteMeasure_apply (μ : ProbabilityMeasure Ω) (s : Set Ω) :
    μ.toFiniteMeasure s = μ s := rfl

@[simp]
/--
theorem `toMeasure_comp_toFiniteMeasure_eq_toMeasure` / 定理 `toMeasure_comp_toFiniteMeasure_eq_toMeasure`

English:
theorem toMeasure_comp_toFiniteMeasure_eq_toMeasure
  given: (ν : ProbabilityMeasure Ω)
  proof: rfl

@[simp]

中文:
定理 toMeasure_comp_toFiniteMeasure_eq_toMeasure
  条件: (ν : ProbabilityMeasure Ω)
  证明: rfl

@[simp]
-/
theorem toMeasure_comp_toFiniteMeasure_eq_toMeasure (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Measure Ω) = (ν : Measure Ω) := rfl

@[simp]
/--
theorem `coeFn_comp_toFiniteMeasure_eq_coeFn` / 定理 `coeFn_comp_toFiniteMeasure_eq_coeFn`

English:
theorem coeFn_comp_toFiniteMeasure_eq_coeFn
  given: (ν : ProbabilityMeasure Ω)
  proof: rfl

@[simp]

中文:
定理 coeFn_comp_toFiniteMeasure_eq_coeFn
  条件: (ν : ProbabilityMeasure Ω)
  证明: rfl

@[simp]
-/
theorem coeFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Set Ω -> Real>=0) = (ν : Set Ω -> Real>=0) := rfl

@[simp]
/--
theorem `toFiniteMeasure_apply_eq_apply` / 定理 `toFiniteMeasure_apply_eq_apply`

English:
theorem toFiniteMeasure_apply_eq_apply
  given: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  proof: rfl

@[simp]

中文:
定理 toFiniteMeasure_apply_eq_apply
  条件: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  证明: rfl

@[simp]
-/
theorem toFiniteMeasure_apply_eq_apply (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ν.toFiniteMeasure s = ν s := rfl

@[simp]
/--
theorem `ennreal_coeFn_eq_coeFn_toMeasure` / 定理 `ennreal_coeFn_eq_coeFn_toMeasure`

English:
theorem ennreal_coeFn_eq_coeFn_toMeasure
  given: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  proof: by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]; rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]; rw [toMeasure_comp_toFiniteMeasure_eq_toMeasure]

@[simp]

中文:
定理 ennreal_coeFn_eq_coeFn_toMeasure
  条件: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  证明: by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]; rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]; rw [toMeasure_comp_toFiniteMeasure_eq_toMeasure]

@[simp]

Depends on / 依赖: FiniteMeasure, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, coeFn_comp_toFiniteMeasure_eq_coeFn, ennreal_coeFn_eq_coeFn_toMeasure, toMeasure_comp_toFiniteMeasure_eq_toMeasure
-/
theorem ennreal_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    (ν s : Real>=0∞) = (ν : Measure Ω) s := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]; rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]; rw [toMeasure_comp_toFiniteMeasure_eq_toMeasure]

@[simp]
/--
theorem `null_iff_toMeasure_null` / 定理 `null_iff_toMeasure_null`

English:
theorem null_iff_toMeasure_null
  given: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  proof: ⟨fun h => by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h => congrArg ENNReal.toNNReal h⟩

@[gcongr]

中文:
定理 null_iff_toMeasure_null
  条件: (ν : ProbabilityMeasure Ω) (s : Set Ω)
  证明: ⟨fun h => by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h => congrArg ENNReal.toNNReal h⟩

@[gcongr]

Depends on / 依赖: ENNReal, ENNReal.coe_zero, ENNReal.toNNReal, coe_zero, ennreal_coeFn_eq_coeFn_toMeasure, toNNReal
-/
theorem null_iff_toMeasure_null (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ν s = 0 ↔ (ν : Measure Ω) s = 0 :=
  ⟨fun h => by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h => congrArg ENNReal.toNNReal h⟩

@[gcongr]
/--
theorem `apply_mono` / 定理 `apply_mono`

English:
theorem apply_mono
  given: (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂)
  statement: μ s₁ <= μ s₂
  proof: by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_mono _ h

中文:
定理 apply_mono
  条件: (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂)
  结论: μ s₁ <= μ s₂
  证明: by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_mono _ h

Depends on / 依赖: FiniteMeasure, FiniteMeasure.apply_mono, apply_mono, coeFn_comp_toFiniteMeasure_eq_coeFn
-/
theorem apply_mono (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂) : μ s₁ <= μ s₂ := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_mono _ h

/--
theorem `apply_union_le` / 定理 `apply_union_le`

English:
theorem apply_union_le
  given: (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω}
  statement: μ (s₁ union s₂) <= μ s₁ + μ s₂
  proof: by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_union_le _

中文:
定理 apply_union_le
  条件: (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω}
  结论: μ (s₁ union s₂) <= μ s₁ + μ s₂
  证明: by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_union_le _

Depends on / 依赖: FiniteMeasure, FiniteMeasure.apply_union_le, apply_union_le, coeFn_comp_toFiniteMeasure_eq_coeFn
-/
theorem apply_union_le (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} : μ (s₁ union s₂) <= μ s₁ + μ s₂ := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_union_le _

/--
lemma `tendsto_measure_iUnion_accumulate` / 引理 `tendsto_measure_iUnion_accumulate`

English:
lemma tendsto_measure_iUnion_accumulate
  statement: {ι : Type*} [Preorder ι]
  proof: by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure)

中文:
引理 tendsto_measure_iUnion_accumulate
  结论: {ι : 类型} [Preorder ι]
  证明: by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure)
-/
protected lemma tendsto_measure_iUnion_accumulate {ι : Type*} [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {μ : ProbabilityMeasure Ω} {f : ι -> Set Ω} :
    Tendsto (fun i => μ (accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure)

/--
theorem `apply_le_one` / 定理 `apply_le_one`

English:
theorem apply_le_one
  given: (μ : ProbabilityMeasure Ω) (s : Set Ω)
  statement: μ s <= 1
  proof: by
  simpa using apply_mono μ (subset_univ s)

中文:
定理 apply_le_one
  条件: (μ : ProbabilityMeasure Ω) (s : Set Ω)
  结论: μ s <= 1
  证明: by
  simpa using apply_mono μ (subset_univ s)
-/
@[simp] theorem apply_le_one (μ : ProbabilityMeasure Ω) (s : Set Ω) : μ s <= 1 := by
  simpa using apply_mono μ (subset_univ s)

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (μ : ProbabilityMeasure Ω)
  statement: Nonempty Ω
  proof: nonempty_of_isProbabilityMeasure μ

@[ext]

中文:
定理 nonempty
  条件: (μ : ProbabilityMeasure Ω)
  结论: Nonempty Ω
  证明: nonempty_of_isProbabilityMeasure μ

@[ext]

Depends on / 依赖: nonempty_of_isProbabilityMeasure
-/
theorem nonempty (μ : ProbabilityMeasure Ω) : Nonempty Ω :=
  nonempty_of_isProbabilityMeasure μ

@[ext]
/--
theorem `eq_of_forall_toMeasure_apply_eq` / 定理 `eq_of_forall_toMeasure_apply_eq`

English:
theorem eq_of_forall_toMeasure_apply_eq
  statement: (μ ν : ProbabilityMeasure Ω)
  proof: by
  apply toMeasure_injective
  ext1 s s_mble
  exact h s s_mble

中文:
定理 eq_of_forall_toMeasure_apply_eq
  结论: (μ ν : ProbabilityMeasure Ω)
  证明: by
  apply toMeasure_injective
  ext1 s s_mble
  exact h s s_mble

Depends on / 依赖: s_mble, toMeasure_injective
-/
theorem eq_of_forall_toMeasure_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : forall s : Set Ω, MeasurableSet s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν := by
  apply toMeasure_injective
  ext1 s s_mble
  exact h s s_mble

/--
theorem `eq_of_forall_apply_eq` / 定理 `eq_of_forall_apply_eq`

English:
theorem eq_of_forall_apply_eq
  statement: (μ ν : ProbabilityMeasure Ω)
  proof: by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : Real>=0 -> Real>=0∞) (h s s_mble)

@[simp]

中文:
定理 eq_of_forall_apply_eq
  结论: (μ ν : ProbabilityMeasure Ω)
  证明: by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : Real>=0 -> Real>=0∞) (h s s_mble)

@[simp]

Depends on / 依赖: congr_arg, ennreal_coeFn_eq_coeFn_toMeasure, s_mble
-/
theorem eq_of_forall_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : forall s : Set Ω, MeasurableSet s -> μ s = ν s) : μ = ν := by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : Real>=0 -> Real>=0∞) (h s s_mble)

@[simp]
/--
theorem `mass_toFiniteMeasure` / 定理 `mass_toFiniteMeasure`

English:
theorem mass_toFiniteMeasure
  given: (μ : ProbabilityMeasure Ω)
  statement: μ.toFiniteMeasure.mass = 1
  proof: μ.coeFn_univ

中文:
定理 mass_toFiniteMeasure
  条件: (μ : ProbabilityMeasure Ω)
  结论: μ.toFiniteMeasure.mass = 1
  证明: μ.coeFn_univ

Depends on / 依赖: coeFn_univ
-/
theorem mass_toFiniteMeasure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass = 1 :=
  μ.coeFn_univ

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `range_toFiniteMeasure` / 引理 `range_toFiniteMeasure`

English:
lemma range_toFiniteMeasure
  proof: by
  ext μ
  simp only [mem_range, mem_ofPred_eq]
  refine ⟨fun ⟨ν, hν⟩ => by simp [← hν], fun h => ?_⟩
  refine ⟨⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using! h)⟩, ?_⟩
  ext s hs
  simp

中文:
引理 range_toFiniteMeasure
  证明: by
  ext μ
  simp only [mem_range, mem_ofPred_eq]
  refine ⟨fun ⟨ν, hν⟩ => by simp [← hν], fun h => ?_⟩
  refine ⟨⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using! h)⟩, ?_⟩
  ext s hs
  simp
-/
@[simp] lemma range_toFiniteMeasure :
    range toFiniteMeasure = {μ : FiniteMeasure Ω | μ.mass = 1} := by
  ext μ
  simp only [mem_range, mem_ofPred_eq]
  refine ⟨fun ⟨ν, hν⟩ => by simp [← hν], fun h => ?_⟩
  refine ⟨⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using! h)⟩, ?_⟩
  ext s hs
  simp

/--
theorem `toFiniteMeasure_nonzero` / 定理 `toFiniteMeasure_nonzero`

English:
theorem toFiniteMeasure_nonzero
  given: (μ : ProbabilityMeasure Ω)
  statement: μ.toFiniteMeasure != 0
  proof: by
  simp [← FiniteMeasure.mass_nonzero_iff]

中文:
定理 toFiniteMeasure_nonzero
  条件: (μ : ProbabilityMeasure Ω)
  结论: μ.toFiniteMeasure != 0
  证明: by
  simp [← FiniteMeasure.mass_nonzero_iff]

Depends on / 依赖: FiniteMeasure, FiniteMeasure.mass_nonzero_iff, mass_nonzero_iff
-/
theorem toFiniteMeasure_nonzero (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure != 0 := by
  simp [← FiniteMeasure.mass_nonzero_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MeasurableSpace (ProbabilityMeasure Ω)
  body: inferInstanceAs MeasurableSpace (Subtype _)

中文:
实例 :
  签名: MeasurableSpace (ProbabilityMeasure Ω)
  定义体: inferInstanceAs MeasurableSpace (Subtype _)

Depends on / 依赖: MeasurableSpace, Subtype
-/
instance : MeasurableSpace (ProbabilityMeasure Ω) :=
inferInstanceAs MeasurableSpace (Subtype _)

/--
lemma `measurableSet_isProbabilityMeasure` / 引理 `measurableSet_isProbabilityMeasure`

English:
lemma measurableSet_isProbabilityMeasure
  proof: by
  suffices { μ : Measure Ω | IsProbabilityMeasure μ } = (fun μ => μ univ) ⁻¹' {1} by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  ext _
  apply isProbabilityMeasure_iff

中文:
引理 measurableSet_isProbabilityMeasure
  证明: by
  suffices { μ : Measure Ω | IsProbabilityMeasure μ } = (fun μ => μ univ) ⁻¹' {1} by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  ext _
  apply isProbabilityMeasure_iff

Depends on / 依赖: IsProbabilityMeasure, MeasurableSet, MeasurableSet.univ, Measure, Measure.measurable_coe, isProbabilityMeasure_iff, measurableSet_singleton, measurable_coe
-/
lemma measurableSet_isProbabilityMeasure :
    MeasurableSet { μ : Measure Ω | IsProbabilityMeasure μ } := by
  suffices { μ : Measure Ω | IsProbabilityMeasure μ } = (fun μ => μ univ) ⁻¹' {1} by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  ext _
  apply isProbabilityMeasure_iff

/--
theorem `measurable_fun_prod` / 定理 `measurable_fun_prod`

English:
theorem measurable_fun_prod
  given: {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  proof: by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm
    isPiSystem_prod _
  simp only [mem_image2, mem_ofPred_eq, forall_exists_index, and_imp]
  intro _ u Hu v Hv Heq
  simp_rw [← Heq, Measure.prod_prod]
  apply Measurable.mul
  · exact (Measure.measurable_coe

中文:
定理 measurable_fun_prod
  条件: {α β : 类型} [MeasurableSpace α] [MeasurableSpace β]
  证明: by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm
    isPiSystem_prod _
  simp only [mem_image2, mem_ofPred_eq, forall_exists_index, and_imp]
  intro _ u Hu v Hv Heq
  simp_rw [← Heq, Measure.prod_prod]
  apply Measurable.mul
  · exact (Measure.measurable_coe

Depends on / 依赖: Measurable, Measurable.measure_of_isPiSystem_of_isProbabilityMeasure, Measurable.mul, Measure, Measure.measurable_coe, Measure.prod_prod, and_imp, forall_exists_index, generateFrom_prod, generateFrom_prod.symm, isPiSystem_prod, measurable_coe, measurable_fst, measurable_snd, measurable_subtype_coe, measurable_subtype_coe.comp, measure_of_isPiSystem_of_isProbabilityMeasure, mem_image2, mem_ofPred_eq, prod_prod
-/
theorem measurable_fun_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (fun (μ : ProbabilityMeasure α × ProbabilityMeasure β)
      => μ.1.toMeasure.prod μ.2.toMeasure) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm
    isPiSystem_prod _
  simp only [mem_image2, mem_ofPred_eq, forall_exists_index, and_imp]
  intro _ u Hu v Hv Heq
  simp_rw [← Heq, Measure.prod_prod]
  apply Measurable.mul
  · exact (Measure.measurable_coe Hu).comp (measurable_subtype_coe.comp measurable_fst)
  · exact (Measure.measurable_coe Hv).comp (measurable_subtype_coe.comp measurable_snd)

/--
lemma `apply_iUnion_le` / 引理 `apply_iUnion_le`

English:
lemma apply_iUnion_le
  statement: {μ : ProbabilityMeasure Ω} {f : Nat -> Set Ω}
  proof: by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

中文:
引理 apply_iUnion_le
  结论: {μ : ProbabilityMeasure Ω} {f : 自然数 -> Set Ω}
  证明: by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_tsum, MeasureTheory, MeasureTheory.measure_iUnion_le, coe_le_coe, coe_tsum, measure_iUnion_le
-/
lemma apply_iUnion_le {μ : ProbabilityMeasure Ω} {f : Nat -> Set Ω}
    (hf : Summable fun n => μ (f n)) :
    μ (⋃ n, f n) <= ∑' n, μ (f n) := by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

section convergence_in_distribution

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/--
theorem `testAgainstNN_lipschitz` / 定理 `testAgainstNN_lipschitz`

English:
theorem testAgainstNN_lipschitz
  given: (μ : ProbabilityMeasure Ω)
  proof: μ.mass_toFiniteMeasure ▸ μ.toFiniteMeasure.testAgainstNN_lipschitz

中文:
定理 testAgainstNN_lipschitz
  条件: (μ : ProbabilityMeasure Ω)
  证明: μ.mass_toFiniteMeasure ▸ μ.toFiniteMeasure.testAgainstNN_lipschitz

Depends on / 依赖: mass_toFiniteMeasure, testAgainstNN_lipschitz, toFiniteMeasure, toFiniteMeasure.testAgainstNN_lipschitz
-/
theorem testAgainstNN_lipschitz (μ : ProbabilityMeasure Ω) :
    LipschitzWith 1 fun f : Ω ->ᵇ Real>=0 => μ.toFiniteMeasure.testAgainstNN f :=
  μ.mass_toFiniteMeasure ▸ μ.toFiniteMeasure.testAgainstNN_lipschitz

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (ProbabilityMeasure Ω)
  body: TopologicalSpace.induced toFiniteMeasure inferInstance

中文:
实例 :
  签名: TopologicalSpace (ProbabilityMeasure Ω)
  定义体: TopologicalSpace.induced toFiniteMeasure inferInstance

Depends on / 依赖: TopologicalSpace, TopologicalSpace.induced, induced, toFiniteMeasure
-/
instance : TopologicalSpace (ProbabilityMeasure Ω) :=
  TopologicalSpace.induced toFiniteMeasure inferInstance

/--
theorem `toFiniteMeasure_continuous` / 定理 `toFiniteMeasure_continuous`

English:
theorem toFiniteMeasure_continuous
  proof: continuous_induced_dom

中文:
定理 toFiniteMeasure_continuous
  证明: continuous_induced_dom

Depends on / 依赖: continuous_induced_dom
-/
theorem toFiniteMeasure_continuous :
    Continuous (toFiniteMeasure : ProbabilityMeasure Ω -> FiniteMeasure Ω) :=
  continuous_induced_dom

/--
Definition of `toWeakDualBCNN` / `toWeakDualBCNN` 的定义

English:
definition toWeakDualBCNN
  signature: : ProbabilityMeasure Ω -> WeakDual Real>=0 (Ω ->ᵇ Real>=0)
  body: FiniteMeasure.toWeakDualBCNN ∘ toFiniteMeasure

@[simp]

中文:
定义 toWeakDualBCNN
  签名: : ProbabilityMeasure Ω -> WeakDual 实数>=0 (Ω ->ᵇ 实数>=0)
  定义体: FiniteMeasure.toWeakDualBCNN ∘ toFiniteMeasure

@[simp]

Depends on / 依赖: FiniteMeasure, FiniteMeasure.toWeakDualBCNN, toFiniteMeasure, toWeakDualBCNN
-/
def toWeakDualBCNN : ProbabilityMeasure Ω -> WeakDual Real>=0 (Ω ->ᵇ Real>=0) :=
  FiniteMeasure.toWeakDualBCNN ∘ toFiniteMeasure

@[simp]
/--
theorem `coe_toWeakDualBCNN` / 定理 `coe_toWeakDualBCNN`

English:
theorem coe_toWeakDualBCNN
  given: (μ : ProbabilityMeasure Ω)
  proof: rfl

@[simp]

中文:
定理 coe_toWeakDualBCNN
  条件: (μ : ProbabilityMeasure Ω)
  证明: rfl

@[simp]
-/
theorem coe_toWeakDualBCNN (μ : ProbabilityMeasure Ω) :
    ⇑μ.toWeakDualBCNN = μ.toFiniteMeasure.testAgainstNN := rfl

@[simp]
/--
theorem `toWeakDualBCNN_apply` / 定理 `toWeakDualBCNN_apply`

English:
theorem toWeakDualBCNN_apply
  given: (μ : ProbabilityMeasure Ω) (f : Ω ->ᵇ Real>=0)
  proof: rfl

中文:
定理 toWeakDualBCNN_apply
  条件: (μ : ProbabilityMeasure Ω) (f : Ω ->ᵇ 实数>=0)
  证明: rfl
-/
theorem toWeakDualBCNN_apply (μ : ProbabilityMeasure Ω) (f : Ω ->ᵇ Real>=0) :
    μ.toWeakDualBCNN f = (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal := rfl

/--
theorem `toWeakDualBCNN_continuous` / 定理 `toWeakDualBCNN_continuous`

English:
theorem toWeakDualBCNN_continuous
  statement: Continuous fun μ : ProbabilityMeasure Ω => μ.toWeakDualBCNN
  proof: FiniteMeasure.toWeakDualBCNN_continuous.comp toFiniteMeasure_continuous

中文:
定理 toWeakDualBCNN_continuous
  结论: Continuous fun μ : ProbabilityMeasure Ω => μ.toWeakDualBCNN
  证明: FiniteMeasure.toWeakDualBCNN_continuous.comp toFiniteMeasure_continuous

Depends on / 依赖: FiniteMeasure, FiniteMeasure.toWeakDualBCNN_continuous.comp, toFiniteMeasure_continuous, toWeakDualBCNN_continuous
-/
theorem toWeakDualBCNN_continuous : Continuous fun μ : ProbabilityMeasure Ω => μ.toWeakDualBCNN :=
  FiniteMeasure.toWeakDualBCNN_continuous.comp toFiniteMeasure_continuous

/--
theorem `continuous_testAgainstNN_eval` / 定理 `continuous_testAgainstNN_eval`

English:
theorem continuous_testAgainstNN_eval
  given: (f : Ω ->ᵇ Real>=0)
  proof: (FiniteMeasure.continuous_testAgainstNN_eval f).comp toFiniteMeasure_continuous

中文:
定理 continuous_testAgainstNN_eval
  条件: (f : Ω ->ᵇ 实数>=0)
  证明: (FiniteMeasure.continuous_testAgainstNN_eval f).comp toFiniteMeasure_continuous

Depends on / 依赖: FiniteMeasure, FiniteMeasure.continuous_testAgainstNN_eval, continuous_testAgainstNN_eval, toFiniteMeasure_continuous
-/
theorem continuous_testAgainstNN_eval (f : Ω ->ᵇ Real>=0) :
    Continuous fun μ : ProbabilityMeasure Ω => μ.toFiniteMeasure.testAgainstNN f :=
  (FiniteMeasure.continuous_testAgainstNN_eval f).comp toFiniteMeasure_continuous

/--
theorem `toFiniteMeasure_isEmbedding` / 定理 `toFiniteMeasure_isEmbedding`

English:
theorem toFiniteMeasure_isEmbedding
  statement: (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω]
  proof: rfl
injective _μ _ν h := Subtype.ext congr_arg FiniteMeasure.toMeasure h

中文:
定理 toFiniteMeasure_isEmbedding
  结论: (Ω : 类型) [MeasurableSpace Ω] [TopologicalSpace Ω]
  证明: rfl
injective _μ _ν h := Subtype.ext congr_arg FiniteMeasure.toMeasure h
-/
theorem toFiniteMeasure_isEmbedding (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] :
    IsEmbedding (toFiniteMeasure : ProbabilityMeasure Ω -> FiniteMeasure Ω) where
  eq_induced := rfl
injective _μ _ν h := Subtype.ext congr_arg FiniteMeasure.toMeasure h

/--
Instance `R1Space` / 实例 `R1Space`

English:
instance R1Space
  signature: : R1Space (ProbabilityMeasure Ω)
  body: (toFiniteMeasure_isEmbedding Ω).r1Space

中文:
实例 R1Space
  签名: : R1Space (ProbabilityMeasure Ω)
  定义体: (toFiniteMeasure_isEmbedding Ω).r1Space

Depends on / 依赖: r1Space, toFiniteMeasure_isEmbedding
-/
instance R1Space : R1Space (ProbabilityMeasure Ω) := (toFiniteMeasure_isEmbedding Ω).r1Space

/--
theorem `tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds` / 定理 `tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds`

English:
theorem tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
  statement: {δ : Type*} (F : Filter δ)
  proof: (toFiniteMeasure_isEmbedding Ω).tendsto_nhds_iff

中文:
定理 tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
  结论: {δ : 类型} (F : Filter δ)
  证明: (toFiniteMeasure_isEmbedding Ω).tendsto_nhds_iff

Depends on / 依赖: tendsto_nhds_iff, toFiniteMeasure_isEmbedding
-/
theorem tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ)
    {μs : δ -> ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ₀) ↔ Tendsto (toFiniteMeasure ∘ μs) F (𝓝 μ₀.toFiniteMeasure) :=
  (toFiniteMeasure_isEmbedding Ω).tendsto_nhds_iff

/--
theorem `tendsto_iff_forall_lintegral_tendsto` / 定理 `tendsto_iff_forall_lintegral_tendsto`

English:
theorem tendsto_iff_forall_lintegral_tendsto
  statement: {γ : Type*} {F : Filter γ}
  proof: by
  rw [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  exact FiniteMeasure.tendsto_iff_forall_lintegral_tendsto

中文:
定理 tendsto_iff_forall_lintegral_tendsto
  结论: {γ : 类型} {F : Filter γ}
  证明: by
  rw [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  exact FiniteMeasure.tendsto_iff_forall_lintegral_tendsto

Depends on / 依赖: FiniteMeasure, FiniteMeasure.tendsto_iff_forall_lintegral_tendsto, tendsto_iff_forall_lintegral_tendsto, tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
-/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ -> ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      forall f : Ω ->ᵇ Real>=0,
        Tendsto (fun i => ∫⁻ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ ω, f ω ∂(μ : Measure Ω))) := by
  rw [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  exact FiniteMeasure.tendsto_iff_forall_lintegral_tendsto

/--
theorem `tendsto_iff_forall_integral_tendsto` / 定理 `tendsto_iff_forall_integral_tendsto`

English:
theorem tendsto_iff_forall_integral_tendsto
  statement: {γ : Type*} {F : Filter γ}
  proof: by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_tendsto]

中文:
定理 tendsto_iff_forall_integral_tendsto
  结论: {γ : 类型} {F : Filter γ}
  证明: by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_tendsto]

Depends on / 依赖: FiniteMeasure, FiniteMeasure.tendsto_iff_forall_integral_tendsto, tendsto_iff_forall_integral_tendsto, tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
-/
theorem tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ -> ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      forall f : Ω ->ᵇ Real,
        Tendsto (fun i => ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_tendsto]

/--
theorem `tendsto_iff_forall_integral_rclike_tendsto` / 定理 `tendsto_iff_forall_integral_rclike_tendsto`

English:
theorem tendsto_iff_forall_integral_rclike_tendsto
  statement: {γ : Type*} (𝕜 : Type*) [RCLike 𝕜]
  proof: by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]

中文:
定理 tendsto_iff_forall_integral_rclike_tendsto
  结论: {γ : 类型} (𝕜 : 类型) [RCLike 𝕜]
  证明: by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]

Depends on / 依赖: FiniteMeasure, FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto, tendsto_iff_forall_integral_rclike_tendsto, tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
-/
theorem tendsto_iff_forall_integral_rclike_tendsto {γ : Type*} (𝕜 : Type*) [RCLike 𝕜]
    {F : Filter γ} {μs : γ -> ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      forall f : Ω ->ᵇ 𝕜,
        Tendsto (fun i => ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]

variable {X : Type*} [TopologicalSpace X] {μs : X -> ProbabilityMeasure Ω}

/--
lemma `continuous_iff_forall_continuous_lintegral` / 引理 `continuous_iff_forall_continuous_lintegral`

English:
lemma continuous_iff_forall_continuous_lintegral
  proof: by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_lintegral_tendsto,
    forall_comm (α := X)]

中文:
引理 continuous_iff_forall_continuous_lintegral
  证明: by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_lintegral_tendsto,
    forall_comm (α := X)]

Depends on / 依赖: ContinuousAt, continuous_iff_continuousAt, forall_comm, tendsto_iff_forall_lintegral_tendsto
-/
lemma continuous_iff_forall_continuous_lintegral :
    Continuous μs ↔ forall f : Ω ->ᵇ Real>=0, Continuous fun x => ∫⁻ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_lintegral_tendsto,
    forall_comm (α := X)]

/--
lemma `continuous_iff_forall_continuous_integral` / 引理 `continuous_iff_forall_continuous_integral`

English:
lemma continuous_iff_forall_continuous_integral
  proof: by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_integral_tendsto,
    forall_comm (α := X)]

中文:
引理 continuous_iff_forall_continuous_integral
  证明: by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_integral_tendsto,
    forall_comm (α := X)]

Depends on / 依赖: ContinuousAt, continuous_iff_continuousAt, forall_comm, tendsto_iff_forall_integral_tendsto
-/
lemma continuous_iff_forall_continuous_integral :
    Continuous μs ↔ forall f : Ω ->ᵇ Real, Continuous fun x => ∫ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_integral_tendsto,
    forall_comm (α := X)]

/--
lemma `continuous_lintegral_boundedContinuousFunction` / 引理 `continuous_lintegral_boundedContinuousFunction`

English:
lemma continuous_lintegral_boundedContinuousFunction
  statement: [MeasurableSpace X] [OpensMeasurableSpace X]
  proof: continuous_iff_forall_continuous_lintegral.1 continuous_id _

中文:
引理 continuous_lintegral_boundedContinuousFunction
  结论: [MeasurableSpace X] [OpensMeasurableSpace X]
  证明: continuous_iff_forall_continuous_lintegral.1 continuous_id _

Depends on / 依赖: continuous_id, continuous_iff_forall_continuous_lintegral
-/
lemma continuous_lintegral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X ->ᵇ Real>=0) : Continuous fun μ : ProbabilityMeasure X => ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuous_lintegral.1 continuous_id _

/--
lemma `continuous_integral_boundedContinuousFunction` / 引理 `continuous_integral_boundedContinuousFunction`

English:
lemma continuous_integral_boundedContinuousFunction
  statement: [MeasurableSpace X] [OpensMeasurableSpace X]
  proof: continuous_iff_forall_continuous_integral.1 continuous_id _

中文:
引理 continuous_integral_boundedContinuousFunction
  结论: [MeasurableSpace X] [OpensMeasurableSpace X]
  证明: continuous_iff_forall_continuous_integral.1 continuous_id _

Depends on / 依赖: continuous_id, continuous_iff_forall_continuous_integral
-/
lemma continuous_integral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X ->ᵇ Real) : Continuous fun μ : ProbabilityMeasure X => ∫ x, f x ∂μ :=
  continuous_iff_forall_continuous_integral.1 continuous_id _

variable [CompactSpace Ω]

/--
lemma `continuous_iff_forall_continuousMap_continuous_lintegral` / 引理 `continuous_iff_forall_continuousMap_continuous_lintegral`

English:
lemma continuous_iff_forall_continuousMap_continuous_lintegral
  proof: continuous_iff_forall_continuous_lintegral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

中文:
引理 continuous_iff_forall_continuousMap_continuous_lintegral
  证明: continuous_iff_forall_continuous_lintegral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

Depends on / 依赖: ContinuousMap, ContinuousMap.equivBoundedOfCompact, continuous_iff_forall_continuous_lintegral, continuous_iff_forall_continuous_lintegral.trans, equivBoundedOfCompact, forall_congr_left, symm.forall_congr_left
-/
lemma continuous_iff_forall_continuousMap_continuous_lintegral :
    Continuous μs ↔ forall f : C(Ω, Real>=0), Continuous fun x => ∫⁻ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_lintegral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

/--
lemma `continuous_iff_forall_continuousMap_continuous_integral` / 引理 `continuous_iff_forall_continuousMap_continuous_integral`

English:
lemma continuous_iff_forall_continuousMap_continuous_integral
  proof: continuous_iff_forall_continuous_integral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

中文:
引理 continuous_iff_forall_continuousMap_continuous_integral
  证明: continuous_iff_forall_continuous_integral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

Depends on / 依赖: ContinuousMap, ContinuousMap.equivBoundedOfCompact, continuous_iff_forall_continuous_integral, continuous_iff_forall_continuous_integral.trans, equivBoundedOfCompact, forall_congr_left, symm.forall_congr_left
-/
lemma continuous_iff_forall_continuousMap_continuous_integral :
    Continuous μs ↔ forall f : C(Ω, Real), Continuous fun x => ∫ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_integral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

variable [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {F : Type*}

/--
lemma `continuous_lintegral_continuousMap` / 引理 `continuous_lintegral_continuousMap`

English:
lemma continuous_lintegral_continuousMap
  given: [FunLike F X Real>=0] [ContinuousMapClass F X Real>=0] (f : F)
  proof: continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩

中文:
引理 continuous_lintegral_continuousMap
  条件: [FunLike F X 实数>=0] [ContinuousMapClass F X 实数>=0] (f : F)
  证明: continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩

Depends on / 依赖: continuous_id, continuous_iff_forall_continuousMap_continuous_lintegral, map_continuous
-/
lemma continuous_lintegral_continuousMap [FunLike F X Real>=0] [ContinuousMapClass F X Real>=0] (f : F) :
    Continuous fun μ : ProbabilityMeasure X => ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩

/--
lemma `continuous_integral_continuousMap` / 引理 `continuous_integral_continuousMap`

English:
lemma continuous_integral_continuousMap
  given: [FunLike F X Real] [ContinuousMapClass F X Real] (f : F)
  proof: continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

中文:
引理 continuous_integral_continuousMap
  条件: [FunLike F X 实数] [ContinuousMapClass F X 实数] (f : F)
  证明: continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

Depends on / 依赖: continuous_id, continuous_iff_forall_continuousMap_continuous_integral, map_continuous
-/
lemma continuous_integral_continuousMap [FunLike F X Real] [ContinuousMapClass F X Real] (f : F) :
    Continuous fun μ : ProbabilityMeasure X => ∫ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

end convergence_in_distribution -- section

section Hausdorff

variable [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
variable (Ω)

/--
Instance `t2Space` / 实例 `t2Space`

English:
instance t2Space
  signature: : T2Space (ProbabilityMeasure Ω)
  body: (toFiniteMeasure_isEmbedding Ω).t2Space

中文:
实例 t2Space
  签名: : T2Space (ProbabilityMeasure Ω)
  定义体: (toFiniteMeasure_isEmbedding Ω).t2Space

Depends on / 依赖: t2Space, toFiniteMeasure_isEmbedding
-/
instance t2Space : T2Space (ProbabilityMeasure Ω) := (toFiniteMeasure_isEmbedding Ω).t2Space

end Hausdorff -- section

end ProbabilityMeasure

-- namespace
end ProbabilityMeasure

-- section
section NormalizeFiniteMeasure

/-! ### Normalization of finite measures to probability measures

This section is about normalizing finite measures to probability measures.

The weak convergence of finite measures to nonzero limit measures is characterized by
the convergence of the total mass and the convergence of the normalized probability
measures.
-/

namespace FiniteMeasure

variable {Ω : Type*} [Nonempty Ω] {m0 : MeasurableSpace Ω} (μ : FiniteMeasure Ω)

/--
Definition of `normalize` / `normalize` 的定义

English:
definition normalize
  signature: : ProbabilityMeasure Ω
  body: if zero : μ.mass = 0 then ⟨Measure.dirac ‹Nonempty Ω›.some, Measure.dirac.isProbabilityMeasure⟩
  else
    { val := μ.mass⁻¹ • (μ : Measure Ω)
      property := by
        refine ⟨?_⟩
        simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
          ENNReal.coe_inv zero, e

中文:
定义 normalize
  签名: : ProbabilityMeasure Ω
  定义体: if zero : μ.mass = 0 then ⟨Measure.dirac ‹Nonempty Ω›.some, Measure.dirac.isProbabilityMeasure⟩
  else
    { val := μ.mass⁻¹ • (μ : Measure Ω)
      property := by
        refine ⟨?_⟩
        simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
          ENNReal.coe_inv zero, e

Depends on / 依赖: ENNReal, ENNReal.coe_inv, ENNReal.coe_ne_zero, ENNReal.inv_mul_cancel, Measure, Measure.coe_smul, Measure.dirac, Measure.dirac.isProbabilityMeasure, Measure.nnreal_smul_coe_apply, Nonempty, Pi.smul_apply, coe_inv, coe_ne_zero, coe_smul, ennreal_mass, inv_mul_cancel, isProbabilityMeasure, measure_univ_lt_top, nnreal_smul_coe_apply, prop.measure_univ_lt_top.ne
-/
def normalize : ProbabilityMeasure Ω :=
  if zero : μ.mass = 0 then ⟨Measure.dirac ‹Nonempty Ω›.some, Measure.dirac.isProbabilityMeasure⟩
  else
    { val := μ.mass⁻¹ • (μ : Measure Ω)
      property := by
        refine ⟨?_⟩
        simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
          ENNReal.coe_inv zero, ennreal_mass]
        rw [← Ne]; rw [← ENNReal.coe_ne_zero]; rw [ennreal_mass] at zero
        exact ENNReal.inv_mul_cancel zero μ.prop.measure_univ_lt_top.ne }

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `self_eq_mass_mul_normalize` / 定理 `self_eq_mass_mul_normalize`

English:
theorem self_eq_mass_mul_normalize
  given: (s : Set Ω)
  statement: μ s = μ.mass * μ.normalize s
  proof: by
  obtain rfl | h := eq_or_ne μ 0
  · simp
  have mass_nonzero : μ.mass != 0 := by rwa [μ.mass_nonzero_iff]
  simp only [normalize, dif_neg mass_nonzero]
  simp [mul_inv_cancel_left₀ mass_nonzero, coeFn_def]

中文:
定理 self_eq_mass_mul_normalize
  条件: (s : Set Ω)
  结论: μ s = μ.mass * μ.normalize s
  证明: by
  obtain rfl | h := eq_or_ne μ 0
  · simp
  have mass_nonzero : μ.mass != 0 := by rwa [μ.mass_nonzero_iff]
  simp only [normalize, dif_neg mass_nonzero]
  simp [mul_inv_cancel_left₀ mass_nonzero, coeFn_def]

Depends on / 依赖: coeFn_def, dif_neg, eq_or_ne, mass_nonzero, mass_nonzero_iff, normalize
-/
theorem self_eq_mass_mul_normalize (s : Set Ω) : μ s = μ.mass * μ.normalize s := by
  obtain rfl | h := eq_or_ne μ 0
  · simp
  have mass_nonzero : μ.mass != 0 := by rwa [μ.mass_nonzero_iff]
  simp only [normalize, dif_neg mass_nonzero]
  simp [mul_inv_cancel_left₀ mass_nonzero, coeFn_def]

/--
theorem `self_eq_mass_smul_normalize` / 定理 `self_eq_mass_smul_normalize`

English:
theorem self_eq_mass_smul_normalize
  statement: μ = μ.mass • μ.normalize.toFiniteMeasure
  proof: by
  apply eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.self_eq_mass_mul_normalize s]; rw [smul_apply]; rw [smul_eq_mul]; rw [ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn]

中文:
定理 self_eq_mass_smul_normalize
  结论: μ = μ.mass • μ.normalize.toFiniteMeasure
  证明: by
  apply eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.self_eq_mass_mul_normalize s]; rw [smul_apply]; rw [smul_eq_mul]; rw [ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn]

Depends on / 依赖: ProbabilityMeasure, ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn, _s_mble, coeFn_comp_toFiniteMeasure_eq_coeFn, eq_of_forall_apply_eq, self_eq_mass_mul_normalize, smul_apply, smul_eq_mul
-/
theorem self_eq_mass_smul_normalize : μ = μ.mass • μ.normalize.toFiniteMeasure := by
  apply eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.self_eq_mass_mul_normalize s]; rw [smul_apply]; rw [smul_eq_mul]; rw [ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn]

/--
theorem `normalize_eq_of_nonzero` / 定理 `normalize_eq_of_nonzero`

English:
theorem normalize_eq_of_nonzero
  given: (nonzero : μ != 0) (s : Set Ω)
  statement: μ.normalize s = μ.mass⁻¹ * μ s
  proof: by
  simp only [μ.self_eq_mass_mul_normalize, μ.mass_nonzero_iff.mpr nonzero, inv_mul_cancel_left₀,
    Ne, not_false_iff]

中文:
定理 normalize_eq_of_nonzero
  条件: (nonzero : μ != 0) (s : Set Ω)
  结论: μ.normalize s = μ.mass⁻¹ * μ s
  证明: by
  simp only [μ.self_eq_mass_mul_normalize, μ.mass_nonzero_iff.mpr nonzero, inv_mul_cancel_left₀,
    Ne, not_false_iff]

Depends on / 依赖: mass_nonzero_iff, mass_nonzero_iff.mpr, nonzero, not_false_iff, self_eq_mass_mul_normalize
-/
theorem normalize_eq_of_nonzero (nonzero : μ != 0) (s : Set Ω) : μ.normalize s = μ.mass⁻¹ * μ s := by
  simp only [μ.self_eq_mass_mul_normalize, μ.mass_nonzero_iff.mpr nonzero, inv_mul_cancel_left₀,
    Ne, not_false_iff]

/--
theorem `normalize_eq_inv_mass_smul_of_nonzero` / 定理 `normalize_eq_inv_mass_smul_of_nonzero`

English:
theorem normalize_eq_inv_mass_smul_of_nonzero
  given: (nonzero : μ != 0)
  proof: by
  nth_rw 3 [μ.self_eq_mass_smul_normalize]
  rw [← smul_assoc]
  simp only [μ.mass_nonzero_iff.mpr nonzero, smul_eq_mul, inv_mul_cancel₀, Ne,
    not_false_iff, one_smul]

中文:
定理 normalize_eq_inv_mass_smul_of_nonzero
  条件: (nonzero : μ != 0)
  证明: by
  nth_rw 3 [μ.self_eq_mass_smul_normalize]
  rw [← smul_assoc]
  simp only [μ.mass_nonzero_iff.mpr nonzero, smul_eq_mul, inv_mul_cancel₀, Ne,
    not_false_iff, one_smul]

Depends on / 依赖: mass_nonzero_iff, mass_nonzero_iff.mpr, nonzero, not_false_iff, nth_rw, one_smul, self_eq_mass_smul_normalize, smul_assoc, smul_eq_mul
-/
theorem normalize_eq_inv_mass_smul_of_nonzero (nonzero : μ != 0) :
    μ.normalize.toFiniteMeasure = μ.mass⁻¹ • μ := by
  nth_rw 3 [μ.self_eq_mass_smul_normalize]
  rw [← smul_assoc]
  simp only [μ.mass_nonzero_iff.mpr nonzero, smul_eq_mul, inv_mul_cancel₀, Ne,
    not_false_iff, one_smul]

/--
theorem `toMeasure_normalize_eq_of_nonzero` / 定理 `toMeasure_normalize_eq_of_nonzero`

English:
theorem toMeasure_normalize_eq_of_nonzero
  given: (nonzero : μ != 0)
  proof: by
  ext1 s _s_mble
  rw [← μ.normalize.ennreal_coeFn_eq_coeFn_toMeasure s]; rw [μ.normalize_eq_of_nonzero nonzero s]; rw [ENNReal.coe_mul]; rw [ennreal_coeFn_eq_coeFn_toMeasure]
  exact Measure.coe_nnreal_smul_apply _ _ _

@[simp]

中文:
定理 toMeasure_normalize_eq_of_nonzero
  条件: (nonzero : μ != 0)
  证明: by
  ext1 s _s_mble
  rw [← μ.normalize.ennreal_coeFn_eq_coeFn_toMeasure s]; rw [μ.normalize_eq_of_nonzero nonzero s]; rw [ENNReal.coe_mul]; rw [ennreal_coeFn_eq_coeFn_toMeasure]
  exact Measure.coe_nnreal_smul_apply _ _ _

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_mul, Measure, Measure.coe_nnreal_smul_apply, _s_mble, coe_mul, coe_nnreal_smul_apply, ennreal_coeFn_eq_coeFn_toMeasure, nonzero, normalize, normalize.ennreal_coeFn_eq_coeFn_toMeasure, normalize_eq_of_nonzero
-/
theorem toMeasure_normalize_eq_of_nonzero (nonzero : μ != 0) :
    (μ.normalize : Measure Ω) = μ.mass⁻¹ • μ := by
  ext1 s _s_mble
  rw [← μ.normalize.ennreal_coeFn_eq_coeFn_toMeasure s]; rw [μ.normalize_eq_of_nonzero nonzero s]; rw [ENNReal.coe_mul]; rw [ennreal_coeFn_eq_coeFn_toMeasure]
  exact Measure.coe_nnreal_smul_apply _ _ _

@[simp]
/--
theorem `_root_.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self` / 定理 `_root_.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self`

English:
theorem _root_.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self
  statement: {m0 : MeasurableSpace Ω}
  proof: by
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.toFiniteMeasure.normalize_eq_of_nonzero μ.toFiniteMeasure_nonzero s]
  simp only [ProbabilityMeasure.mass_toFiniteMeasure, inv_one, one_mul, μ.coeFn_toFiniteMeasure]

中文:
定理 _root_.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self
  结论: {m0 : MeasurableSpace Ω}
  证明: by
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.toFiniteMeasure.normalize_eq_of_nonzero μ.toFiniteMeasure_nonzero s]
  simp only [ProbabilityMeasure.mass_toFiniteMeasure, inv_one, one_mul, μ.coeFn_toFiniteMeasure]

Depends on / 依赖: ProbabilityMeasure, ProbabilityMeasure.eq_of_forall_apply_eq, ProbabilityMeasure.mass_toFiniteMeasure, _s_mble, coeFn_toFiniteMeasure, eq_of_forall_apply_eq, inv_one, mass_toFiniteMeasure, normalize_eq_of_nonzero, one_mul, toFiniteMeasure, toFiniteMeasure.normalize_eq_of_nonzero, toFiniteMeasure_nonzero
-/
theorem _root_.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self {m0 : MeasurableSpace Ω}
    (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.normalize = μ := by
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s _s_mble
  rw [μ.toFiniteMeasure.normalize_eq_of_nonzero μ.toFiniteMeasure_nonzero s]
  simp only [ProbabilityMeasure.mass_toFiniteMeasure, inv_one, one_mul, μ.coeFn_toFiniteMeasure]

/--
theorem `average_eq_integral_normalize` / 定理 `average_eq_integral_normalize`

English:
theorem average_eq_integral_normalize
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [μ.toMeasure_normalize_eq_of_nonzero nonzero]; rw [average]
  congr
  simp [ENNReal.coe_inv (μ.mass_nonzero_iff.mpr nonzero), ennreal_mass]

中文:
定理 average_eq_integral_normalize
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: by
  rw [μ.toMeasure_normalize_eq_of_nonzero nonzero]; rw [average]
  congr
  simp [ENNReal.coe_inv (μ.mass_nonzero_iff.mpr nonzero), ennreal_mass]

Depends on / 依赖: ENNReal, ENNReal.coe_inv, average, coe_inv, ennreal_mass, mass_nonzero_iff, mass_nonzero_iff.mpr, nonzero, toMeasure_normalize_eq_of_nonzero
-/
theorem average_eq_integral_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (nonzero : μ != 0) (f : Ω -> E) :
    average (μ : Measure Ω) f = ∫ ω, f ω ∂(μ.normalize : Measure Ω) := by
  rw [μ.toMeasure_normalize_eq_of_nonzero nonzero]; rw [average]
  congr
  simp [ENNReal.coe_inv (μ.mass_nonzero_iff.mpr nonzero), ennreal_mass]

variable [TopologicalSpace Ω]

/--
theorem `testAgainstNN_eq_mass_mul` / 定理 `testAgainstNN_eq_mass_mul`

English:
theorem testAgainstNN_eq_mass_mul
  given: (f : Ω ->ᵇ Real>=0)
  proof: by
  nth_rw 1 [μ.self_eq_mass_smul_normalize]
  rw [μ.normalize.toFiniteMeasure.smul_testAgainstNN_apply μ.mass f]; rw [smul_eq_mul]

中文:
定理 testAgainstNN_eq_mass_mul
  条件: (f : Ω ->ᵇ 实数>=0)
  证明: by
  nth_rw 1 [μ.self_eq_mass_smul_normalize]
  rw [μ.normalize.toFiniteMeasure.smul_testAgainstNN_apply μ.mass f]; rw [smul_eq_mul]

Depends on / 依赖: normalize, normalize.toFiniteMeasure.smul_testAgainstNN_apply, nth_rw, self_eq_mass_smul_normalize, smul_eq_mul, smul_testAgainstNN_apply, toFiniteMeasure
-/
theorem testAgainstNN_eq_mass_mul (f : Ω ->ᵇ Real>=0) :
    μ.testAgainstNN f = μ.mass * μ.normalize.toFiniteMeasure.testAgainstNN f := by
  nth_rw 1 [μ.self_eq_mass_smul_normalize]
  rw [μ.normalize.toFiniteMeasure.smul_testAgainstNN_apply μ.mass f]; rw [smul_eq_mul]

/--
theorem `normalize_testAgainstNN` / 定理 `normalize_testAgainstNN`

English:
theorem normalize_testAgainstNN
  given: (nonzero : μ != 0) (f : Ω ->ᵇ Real>=0)
  proof: by
  simp [μ.testAgainstNN_eq_mass_mul, inv_mul_cancel_left₀ <| μ.mass_nonzero_iff.mpr nonzero]

中文:
定理 normalize_testAgainstNN
  条件: (nonzero : μ != 0) (f : Ω ->ᵇ 实数>=0)
  证明: by
  simp [μ.testAgainstNN_eq_mass_mul, inv_mul_cancel_left₀ <| μ.mass_nonzero_iff.mpr nonzero]

Depends on / 依赖: mass_nonzero_iff, mass_nonzero_iff.mpr, nonzero, testAgainstNN_eq_mass_mul
-/
theorem normalize_testAgainstNN (nonzero : μ != 0) (f : Ω ->ᵇ Real>=0) :
    μ.normalize.toFiniteMeasure.testAgainstNN f = μ.mass⁻¹ * μ.testAgainstNN f := by
  simp [μ.testAgainstNN_eq_mass_mul, inv_mul_cancel_left₀ <| μ.mass_nonzero_iff.mpr nonzero]

variable [OpensMeasurableSpace Ω]
variable {μ}

/--
theorem `tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass` / 定理 `tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass`

English:
theorem tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  statement: {γ : Type*}
  proof: by
  by_cases h_mass : μ.mass = 0
  · simp only [μ.mass_zero_iff.mp h_mass, zero_testAgainstNN_apply, zero_mass] at mass_lim ⊢
    exact tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  simp_rw [fun i => (μs i).testAgainstNN_eq_mass_mul f, μ.testAgainstNN_eq_mass_mul f]
  rw [Probability

中文:
定理 tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  结论: {γ : 类型}
  证明: by
  by_cases h_mass : μ.mass = 0
  · simp only [μ.mass_zero_iff.mp h_mass, zero_testAgainstNN_apply, zero_mass] at mass_lim ⊢
    exact tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  simp_rw [fun i => (μs i).testAgainstNN_eq_mass_mul f, μ.testAgainstNN_eq_mass_mul f]
  rw [Probability

Depends on / 依赖: ProbabilityMeasure, ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds, Tendsto, h_mass, lim_pair, mass_lim, mass_zero_iff, mass_zero_iff.mp, normalize, normalize.toFiniteMeasure.testAgain, simp_rw, tendsto_iff_forall_testAgainstNN_tendsto, tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds, tendsto_zero_testAgainstNN_of_tendsto_zero_mass, testAgain, testAgainstNN_eq_mass_mul, toFiniteMeasure, zero_mass, zero_testAgainstNN_apply
-/
theorem tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : Type*}
    {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
    (μs_lim : Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize))
    (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass)) (f : Ω ->ᵇ Real>=0) :
    Tendsto (fun i => (μs i).testAgainstNN f) F (𝓝 (μ.testAgainstNN f)) := by
  by_cases h_mass : μ.mass = 0
  · simp only [μ.mass_zero_iff.mp h_mass, zero_testAgainstNN_apply, zero_mass] at mass_lim ⊢
    exact tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  simp_rw [fun i => (μs i).testAgainstNN_eq_mass_mul f, μ.testAgainstNN_eq_mass_mul f]
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds] at μs_lim
  rw [tendsto_iff_forall_testAgainstNN_tendsto] at μs_lim
  have lim_pair :
    Tendsto (fun i => (⟨(μs i).mass, (μs i).normalize.toFiniteMeasure.testAgainstNN f⟩ : Real>=0 × Real>=0))
      F (𝓝 ⟨μ.mass, μ.normalize.toFiniteMeasure.testAgainstNN f⟩) :=
    (Prod.tendsto_iff _ _).mpr ⟨mass_lim, μs_lim f⟩
  exact tendsto_mul.comp lim_pair

/--
theorem `tendsto_normalize_testAgainstNN_of_tendsto` / 定理 `tendsto_normalize_testAgainstNN_of_tendsto`

English:
theorem tendsto_normalize_testAgainstNN_of_tendsto
  statement: {γ : Type*} {F : Filter γ}
  proof: by
  have lim_mass := μs_lim.mass
  have aux : {(0 : Real>=0)}ᶜ in 𝓝 μ.mass :=
    isOpen_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr nonzero)
  have eventually_nonzero : forallᶠ i in F, μs i != 0 := by
    simp_rw [← mass_nonzero_iff]
    exact lim_mass aux
  have eve : forallᶠ i in F,
      (

中文:
定理 tendsto_normalize_testAgainstNN_of_tendsto
  结论: {γ : 类型} {F : Filter γ}
  证明: by
  have lim_mass := μs_lim.mass
  have aux : {(0 : Real>=0)}ᶜ in 𝓝 μ.mass :=
    isOpen_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr nonzero)
  have eventually_nonzero : forallᶠ i in F, μs i != 0 := by
    simp_rw [← mass_nonzero_iff]
    exact lim_mass aux
  have eve : forallᶠ i in F,
      (

Depends on / 依赖: eventually_iff, eventually_iff.mp, eventually_nonzero, filter_upwards, isOpen_compl_singleton, isOpen_compl_singleton.mem_nhds, lim_mass, mass_nonzero_iff, mass_nonzero_iff.mpr, mem_nhds, nonzero, normalize, normalize.toFiniteMeasure.testAgainstNN, normalize_testAgainstNN, s_lim.mass, simp_rw, tendsto_congr, testAgainstNN, toFiniteMeasure
-/
theorem tendsto_normalize_testAgainstNN_of_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ -> FiniteMeasure Ω} (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ != 0) (f : Ω ->ᵇ Real>=0) :
    Tendsto (fun i => (μs i).normalize.toFiniteMeasure.testAgainstNN f) F
      (𝓝 (μ.normalize.toFiniteMeasure.testAgainstNN f)) := by
  have lim_mass := μs_lim.mass
  have aux : {(0 : Real>=0)}ᶜ in 𝓝 μ.mass :=
    isOpen_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr nonzero)
  have eventually_nonzero : forallᶠ i in F, μs i != 0 := by
    simp_rw [← mass_nonzero_iff]
    exact lim_mass aux
  have eve : forallᶠ i in F,
      (μs i).normalize.toFiniteMeasure.testAgainstNN f =
        (μs i).mass⁻¹ * (μs i).testAgainstNN f := by
    filter_upwards [eventually_iff.mp eventually_nonzero]
    intro i hi
    apply normalize_testAgainstNN _ hi
  simp_rw [tendsto_congr' eve, μ.normalize_testAgainstNN nonzero]
  have lim_pair :
    Tendsto (fun i => (⟨(μs i).mass⁻¹, (μs i).testAgainstNN f⟩ : Real>=0 × Real>=0)) F
      (𝓝 ⟨μ.mass⁻¹, μ.testAgainstNN f⟩) := by
    refine (Prod.tendsto_iff _ _).mpr ⟨?_, ?_⟩
    · exact (continuousOn_inv₀.continuousAt aux).tendsto.comp lim_mass
    · exact tendsto_iff_forall_testAgainstNN_tendsto.mp μs_lim f
  exact tendsto_mul.comp lim_pair

/--
theorem `tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass` / 定理 `tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass`

English:
theorem tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  statement: {γ : Type*} {F : Filter γ}
  proof: by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f =>
    tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass μs_lim mass_lim f

中文:
定理 tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  结论: {γ : 类型} {F : Filter γ}
  证明: by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f =>
    tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass μs_lim mass_lim f

Depends on / 依赖: mass_lim, tendsto_iff_forall_testAgainstNN_tendsto, tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
-/
theorem tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass {γ : Type*} {F : Filter γ}
    {μs : γ -> FiniteMeasure Ω} (μs_lim : Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize))
    (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass)) : Tendsto μs F (𝓝 μ) := by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f =>
    tendsto_testAgainstNN_of_tendsto_normalize_testAgainstNN_of_tendsto_mass μs_lim mass_lim f

/--
theorem `tendsto_normalize_of_tendsto` / 定理 `tendsto_normalize_of_tendsto`

English:
theorem tendsto_normalize_of_tendsto
  statement: {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  proof: by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]; rw [tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f => tendsto_normalize_testAgainstNN_of_tendsto μs_lim nonzero f

中文:
定理 tendsto_normalize_of_tendsto
  结论: {γ : 类型} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  证明: by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]; rw [tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f => tendsto_normalize_testAgainstNN_of_tendsto μs_lim nonzero f

Depends on / 依赖: ProbabilityMeasure, ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds, nonzero, tendsto_iff_forall_testAgainstNN_tendsto, tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds, tendsto_normalize_testAgainstNN_of_tendsto
-/
theorem tendsto_normalize_of_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
    (μs_lim : Tendsto μs F (𝓝 μ)) (nonzero : μ != 0) :
    Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize) := by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]; rw [tendsto_iff_forall_testAgainstNN_tendsto]
  exact fun f => tendsto_normalize_testAgainstNN_of_tendsto μs_lim nonzero f

/--
theorem `tendsto_normalize_iff_tendsto` / 定理 `tendsto_normalize_iff_tendsto`

English:
theorem tendsto_normalize_iff_tendsto
  statement: {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  proof: by
  constructor
  · rintro ⟨normalized_lim, mass_lim⟩
    exact tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass normalized_lim mass_lim
  · intro μs_lim
    exact ⟨tendsto_normalize_of_tendsto μs_lim nonzero, μs_lim.mass⟩

中文:
定理 tendsto_normalize_iff_tendsto
  结论: {γ : 类型} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  证明: by
  constructor
  · rintro ⟨normalized_lim, mass_lim⟩
    exact tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass normalized_lim mass_lim
  · intro μs_lim
    exact ⟨tendsto_normalize_of_tendsto μs_lim nonzero, μs_lim.mass⟩

Depends on / 依赖: mass_lim, nonzero, normalized_lim, s_lim.mass, tendsto_normalize_of_tendsto, tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
-/
theorem tendsto_normalize_iff_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
    (nonzero : μ != 0) :
    Tendsto (fun i => (μs i).normalize) F (𝓝 μ.normalize) ∧
        Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass) ↔
      Tendsto μs F (𝓝 μ) := by
  constructor
  · rintro ⟨normalized_lim, mass_lim⟩
    exact tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass normalized_lim mass_lim
  · intro μs_lim
    exact ⟨tendsto_normalize_of_tendsto μs_lim nonzero, μs_lim.mass⟩

end FiniteMeasure --namespace

end NormalizeFiniteMeasure -- section

section map

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

namespace ProbabilityMeasure

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
  body: ⟨(ν : Measure Ω).map f, (ν : Measure Ω).isProbabilityMeasure_map f_aemble⟩

中文:
定义 map
  签名: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
  定义体: ⟨(ν : Measure Ω).map f, (ν : Measure Ω).isProbabilityMeasure_map f_aemble⟩

Depends on / 依赖: Measure, f_aemble, isProbabilityMeasure_map
-/
noncomputable def map (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν) :
    ProbabilityMeasure Ω' :=
  ⟨(ν : Measure Ω).map f, (ν : Measure Ω).isProbabilityMeasure_map f_aemble⟩

/--
lemma `toMeasure_map` / 引理 `toMeasure_map`

English:
lemma toMeasure_map
  given: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (hf : AEMeasurable f ν)
  proof: rfl

中文:
引理 toMeasure_map
  条件: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (hf : AEMeasurable f ν)
  证明: rfl
-/
@[simp] lemma toMeasure_map (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (hf : AEMeasurable f ν) :
    (ν.map hf).toMeasure = ν.toMeasure.map f := rfl

/--
lemma `map_apply'` / 引理 `map_apply'`

English:
lemma map_apply'
  statement: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
  proof: Measure.map_apply_of_aemeasurable f_aemble A_mble

中文:
引理 map_apply'
  结论: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
  证明: Measure.map_apply_of_aemeasurable f_aemble A_mble

Depends on / 依赖: A_mble, Measure, Measure.map_apply_of_aemeasurable, f_aemble, map_apply_of_aemeasurable
-/
lemma map_apply' (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble : Measure Ω') A = (ν : Measure Ω) (f ⁻¹' A) :=
  Measure.map_apply_of_aemeasurable f_aemble A_mble

/--
lemma `map_apply_of_aemeasurable` / 引理 `map_apply_of_aemeasurable`

English:
lemma map_apply_of_aemeasurable
  statement: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'}
  proof: by
exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr
    ν.map_apply' f_aemble A_mble

中文:
引理 map_apply_of_aemeasurable
  结论: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'}
  证明: by
exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr
    ν.map_apply' f_aemble A_mble

Depends on / 依赖: A_mble, ENNReal, ENNReal.toNNReal_eq_toNNReal_iff, f_aemble, map_apply, measure_ne_top, toNNReal_eq_toNNReal_iff
-/
lemma map_apply_of_aemeasurable (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'}
    (f_aemble : AEMeasurable f ν) {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble) A = ν (f ⁻¹' A) := by
exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr
    ν.map_apply' f_aemble A_mble

/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  statement: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
  proof: map_apply_of_aemeasurable ν f_aemble A_mble

中文:
引理 map_apply
  结论: (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
  证明: map_apply_of_aemeasurable ν f_aemble A_mble

Depends on / 依赖: A_mble, f_aemble, map_apply_of_aemeasurable
-/
lemma map_apply (ν : ProbabilityMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f_aemble) A = ν (f ⁻¹' A) :=
  map_apply_of_aemeasurable ν f_aemble A_mble

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
variable [TopologicalSpace Ω'] [BorelSpace Ω']

/--
lemma `tendsto_map_of_tendsto_of_continuous` / 引理 `tendsto_map_of_tendsto_of_continuous`

English:
lemma tendsto_map_of_tendsto_of_continuous
  statement: {ι : Type*} {L : Filter ι}
  proof: by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert! lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).me

中文:
引理 tendsto_map_of_tendsto_of_continuous
  结论: {ι : 类型} {L : Filter ι}
  证明: by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert! lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).me

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, ENNReal, ENNReal.continuous_coe.comp, ProbabilityMeasure, ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, coe_mk, compContinuous, compContinuous_apply, continuous, continuous_coe, convert, f_cont, f_cont.measurable, g.compContinuous, g.continuous, lintegral_map, measurable, tendsto_iff_forall_lintegral_tendsto
-/
lemma tendsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι}
    (νs : ι -> ProbabilityMeasure Ω) (ν : ProbabilityMeasure Ω) (lim : Tendsto νs L (𝓝 ν))
    {f : Ω -> Ω'} (f_cont : Continuous f) :
    Tendsto (fun i => (νs i).map f_cont.measurable.aemeasurable) L
      (𝓝 (ν.map f_cont.measurable.aemeasurable)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert! lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).measurable

/--
lemma `continuous_map` / 引理 `continuous_map`

English:
lemma continuous_map
  given: {f : Ω -> Ω'} (f_cont : Continuous f)
  proof: by
  rw [continuous_iff_continuousAt]
  exact fun _ => tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

中文:
引理 continuous_map
  条件: {f : Ω -> Ω'} (f_cont : Continuous f)
  证明: by
  rw [continuous_iff_continuousAt]
  exact fun _ => tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

Depends on / 依赖: continuousAt, continuous_id, continuous_id.continuousAt, continuous_iff_continuousAt, f_cont, tendsto_map_of_tendsto_of_continuous
-/
lemma continuous_map {f : Ω -> Ω'} (f_cont : Continuous f) :
    Continuous (fun ν => ProbabilityMeasure.map ν f_cont.measurable.aemeasurable) := by
  rw [continuous_iff_continuousAt]
  exact fun _ => tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

end ProbabilityMeasure -- namespace

end map -- section

section join_bind

/--
theorem `isProbabilityMeasure_join` / 定理 `isProbabilityMeasure_join`

English:
theorem isProbabilityMeasure_join
  statement: {α : Type*} [MeasurableSpace α] {m : Measure (Measure α)}
  proof: by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.join_apply]
  simp_rw [isProbabilityMeasure_iff] at hm
  exact lintegral_eq_const hm

中文:
定理 isProbabilityMeasure_join
  结论: {α : 类型} [MeasurableSpace α] {m : Measure (Measure α)}
  证明: by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.join_apply]
  simp_rw [isProbabilityMeasure_iff] at hm
  exact lintegral_eq_const hm

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.join_apply, isProbabilityMeasure_iff, join_apply, lintegral_eq_const, simp_rw
-/
theorem isProbabilityMeasure_join {α : Type*} [MeasurableSpace α] {m : Measure (Measure α)}
    [IsProbabilityMeasure m] (hm : forallᵐ μ ∂m, IsProbabilityMeasure μ) :
    IsProbabilityMeasure (m.join) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.join_apply]
  simp_rw [isProbabilityMeasure_iff] at hm
  exact lintegral_eq_const hm

/--
theorem `isProbabilityMeasure_bind` / 定理 `isProbabilityMeasure_bind`

English:
theorem isProbabilityMeasure_bind
  statement: {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  proof: by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.bind_apply _ hf₀]
  simp_rw [isProbabilityMeasure_iff] at hf₁
  exact lintegral_eq_const hf₁

中文:
定理 isProbabilityMeasure_bind
  结论: {α : 类型} {β : 类型} [MeasurableSpace α] [MeasurableSpace β]
  证明: by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.bind_apply _ hf₀]
  simp_rw [isProbabilityMeasure_iff] at hf₁
  exact lintegral_eq_const hf₁

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.bind_apply, bind_apply, isProbabilityMeasure_iff, lintegral_eq_const, simp_rw
-/
theorem isProbabilityMeasure_bind {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} [IsProbabilityMeasure m] {f : α -> Measure β} (hf₀ : AEMeasurable f m)
    (hf₁ : forallᵐ μ ∂m, IsProbabilityMeasure (f μ)) : IsProbabilityMeasure (m.bind f) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.bind_apply _ hf₀]
  simp_rw [isProbabilityMeasure_iff] at hf₁
  exact lintegral_eq_const hf₁

end join_bind

end MeasureTheory -- namespace
