/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.TietzeExtension

/-!
# Finite measures

This file defines the type of finite measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of finite measures is equipped with the topology of weak convergence
of measures. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

## Main definitions

The main definitions are
* `MeasureTheory.FiniteMeasure Ω`: The type of finite measures on `Ω` with the topology of weak
  convergence of measures.
* `MeasureTheory.FiniteMeasure.toWeakDualBCNN : FiniteMeasure Ω → (WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0))`:
  Interpret a finite measure as a continuous linear functional on the space of
  bounded continuous nonnegative functions on `Ω`. This is used for the definition of the
  topology of weak convergence.
* `MeasureTheory.FiniteMeasure.map`: The push-forward `f* μ` of a finite measure `μ` on `Ω`
  along a measurable function `f : Ω → Ω'`.
* `MeasureTheory.FiniteMeasure.mapCLM`: The push-forward along a given continuous `f : Ω → Ω'`
  as a continuous linear map `f* : FiniteMeasure Ω →L[ℝ≥0] FiniteMeasure Ω'`.

## Main results

* Finite measures `μ` on `Ω` give rise to continuous linear functionals on the space of
  bounded continuous nonnegative functions on `Ω` via integration:
  `MeasureTheory.FiniteMeasure.toWeakDualBCNN : FiniteMeasure Ω → (WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0))`
* `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto`: Convergence of finite
  measures is characterized by the convergence of integrals of all bounded continuous functions.
  This shows that the chosen definition of topology coincides with the common textbook definition
  of weak convergence of measures. A similar characterization by the convergence of integrals (in
  the `MeasureTheory.lintegral` sense) of all bounded continuous nonnegative functions is
  `MeasureTheory.FiniteMeasure.tendsto_iff_forall_lintegral_tendsto`.
* `MeasureTheory.FiniteMeasure.continuous_map`: For a continuous function `f : Ω → Ω'`, the
  push-forward of finite measures `f* : FiniteMeasure Ω → FiniteMeasure Ω'` is continuous.
* `MeasureTheory.FiniteMeasure.t2Space`: The topology of weak convergence of finite Borel measures
  is Hausdorff on spaces where indicators of closed sets have continuous decreasing approximating
  sequences (in particular on any pseudo-metrizable spaces).

## Implementation notes

The topology of weak convergence of finite Borel measures is defined using a mapping from
`MeasureTheory.FiniteMeasure Ω` to `WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0)`, inheriting the topology from the
latter.

The implementation of `MeasureTheory.FiniteMeasure Ω` and is directly as a subtype of
`MeasureTheory.Measure Ω`, and the coercion to a function is the composition `ENNReal.toNNReal`
and the coercion to function of `MeasureTheory.Measure Ω`. Another alternative would have been to
use a bijection with `MeasureTheory.VectorMeasure Ω ℝ≥0` as an intermediate step. Some
considerations:
* Potential advantages of using the `NNReal`-valued vector measure alternative:
  * The coercion to function would avoid need to compose with `ENNReal.toNNReal`, the
    `NNReal`-valued API could be more directly available.
* Potential drawbacks of the vector measure alternative:
  * The coercion to function would lose monotonicity, as non-measurable sets would be defined to
    have measure 0.
  * No integration theory directly. E.g., the topology definition requires
    `MeasureTheory.lintegral` w.r.t. a coercion to `MeasureTheory.Measure Ω` in any case.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure

-/

@[expose] public section


noncomputable section

open BoundedContinuousFunction Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Function

namespace MeasureTheory

namespace FiniteMeasure

section FiniteMeasure

/-! ### Finite measures

In this section we define the `Type` of `MeasureTheory.FiniteMeasure Ω`, when `Ω` is a measurable
space. Finite measures on `Ω` are a module over `ℝ≥0`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[OpensMeasurableSpace Ω]`), then `MeasureTheory.FiniteMeasure Ω` is equipped with
the topology of weak convergence of measures. This is implemented by defining a pairing of finite
measures `μ` on `Ω` with continuous bounded nonnegative functions `f : Ω →ᵇ ℝ≥0` via integration,
and using the associated weak topology (essentially the weak-star topology on the dual of
`Ω →ᵇ ℝ≥0`).
-/


variable {Ω : Type*} [MeasurableSpace Ω] {s t : Set Ω}

/--
Definition of `_root_.MeasureTheory.FiniteMeasure` / `_root_.MeasureTheory.FiniteMeasure` 的定义

English:
definition _root_.MeasureTheory.FiniteMeasure
  signature: (Ω : Type*) [MeasurableSpace Ω]
  body: { μ : Measure Ω // IsFiniteMeasure μ }

中文:
定义 _root_.测度论.有限测度
  签名: (Ω : 类型) [可测空间 Ω]
  定义体: { μ : Measure Ω // IsFiniteMeasure μ }

Depends on / 依赖: IsFiniteMeasure, Measure
-/
def _root_.MeasureTheory.FiniteMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsFiniteMeasure μ }

/-- Coercion from `MeasureTheory.FiniteMeasure Ω` to `MeasureTheory.Measure Ω`. -/
@[coe]
/--
Definition of `toMeasure` / `toMeasure` 的定义

English:
definition toMeasure
  signature: : FiniteMeasure Ω -> Measure Ω
  body: Subtype.val

中文:
定义 toMeasure
  签名: : 有限测度 Ω -> 测度 Ω
  定义体: Subtype.val

Depends on / 依赖: Subtype, Subtype.val
-/
def toMeasure : FiniteMeasure Ω -> Measure Ω := Subtype.val

/--
Instance `instCoe` / 实例 `instCoe`

English:
instance instCoe
  signature: : Coe (FiniteMeasure Ω) (MeasureTheory.Measure Ω)
  body: { coe := toMeasure }

中文:
实例 instCoe
  签名: : Coe (有限测度 Ω) (测度论.测度 Ω)
  定义体: { coe := toMeasure }

Depends on / 依赖: toMeasure
-/
instance instCoe : Coe (FiniteMeasure Ω) (MeasureTheory.Measure Ω) := { coe := toMeasure }

/--
Instance `isFiniteMeasure` / 实例 `isFiniteMeasure`

English:
instance isFiniteMeasure
  signature: (μ : FiniteMeasure Ω)
  body: μ.prop

@[simp]

中文:
实例 isFiniteMeasure
  签名: (μ : 有限测度 Ω)
  定义体: μ.prop

@[simp]
-/
instance isFiniteMeasure (μ : FiniteMeasure Ω) : IsFiniteMeasure (μ : Measure Ω) := μ.prop

@[simp]
/--
theorem `val_eq_toMeasure` / 定理 `val_eq_toMeasure`

English:
theorem val_eq_toMeasure
  given: (ν : FiniteMeasure Ω)
  statement: ν.val = (ν : Measure Ω)
  proof: rfl

中文:
定理 val_eq_toMeasure
  条件: (ν : 有限测度 Ω)
  结论: ν.val = (ν : 测度 Ω)
  证明: rfl
-/
theorem val_eq_toMeasure (ν : FiniteMeasure Ω) : ν.val = (ν : Measure Ω) := rfl

/--
theorem `toMeasure_injective` / 定理 `toMeasure_injective`

English:
theorem toMeasure_injective
  statement: Function.Injective ((↑) : FiniteMeasure Ω -> Measure Ω)
  proof: Subtype.coe_injective

中文:
定理 toMeasure_injective
  结论: 函数.单射 ((↑) : 有限测度 Ω -> 测度 Ω)
  证明: Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem toMeasure_injective : Function.Injective ((↑) : FiniteMeasure Ω -> Measure Ω) :=
  Subtype.coe_injective

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (FiniteMeasure Ω) (Set Ω) Real>=0 where
  body: ((μ : Measure Ω) s).toNNReal
coe_injective μ ν h := toMeasure_injective Measure.ext fun s _ => by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s

中文:
实例 instFunLike
  签名: : 函数状 (有限测度 Ω) (集合 Ω) 实数>=0 where
  定义体: ((μ : Measure Ω) s).toNNReal
coe_injective μ ν h := toMeasure_injective Measure.ext fun s _ => by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s

Depends on / 依赖: Measure, toNNReal
-/
instance instFunLike : FunLike (FiniteMeasure Ω) (Set Ω) Real>=0 where
  coe μ s := ((μ : Measure Ω) s).toNNReal
coe_injective μ ν h := toMeasure_injective Measure.ext fun s _ => by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s

/--
lemma `coeFn_def` / 引理 `coeFn_def`

English:
lemma coeFn_def
  given: (μ : FiniteMeasure Ω)
  statement: μ = fun s => ((μ : Measure Ω) s).toNNReal
  proof: rfl

中文:
引理 coeFn_def
  条件: (μ : 有限测度 Ω)
  结论: μ = fun s => ((μ : 测度 Ω) s).toNN实数
  证明: rfl
-/
lemma coeFn_def (μ : FiniteMeasure Ω) : μ = fun s => ((μ : Measure Ω) s).toNNReal := rfl

/--
lemma `coeFn_mk` / 引理 `coeFn_mk`

English:
lemma coeFn_mk
  given: (μ : Measure Ω) (hμ)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coeFn_mk
  条件: (μ : 测度 Ω) (hμ)
  证明: rfl

@[simp, norm_cast]

Depends on / 依赖: FiniteMeasure, lex_iff_of_unique, toNNReal
-/
lemma coeFn_mk (μ : Measure Ω) (hμ) :
    DFunLike.coe (F := FiniteMeasure Ω) ⟨μ, hμ⟩ = fun s => (μ s).toNNReal := rfl

@[simp, norm_cast]
/--
lemma `mk_apply` / 引理 `mk_apply`

English:
lemma mk_apply
  given: (μ : Measure Ω) (hμ) (s : Set Ω)
  proof: rfl

中文:
引理 mk_apply
  条件: (μ : 测度 Ω) (hμ) (s : 集合 Ω)
  证明: rfl

Depends on / 依赖: FiniteMeasure, lex_iff_of_unique, toNNReal
-/
lemma mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) :
    DFunLike.coe (F := FiniteMeasure Ω) ⟨μ, hμ⟩ s = (μ s).toNNReal := rfl

/--
lemma `toMeasure_mk` / 引理 `toMeasure_mk`

English:
lemma toMeasure_mk
  given: (μ : Measure Ω) (h : IsFiniteMeasure μ)
  proof: rfl

中文:
引理 toMeasure_mk
  条件: (μ : 测度 Ω) (h : 是有限测度 μ)
  证明: rfl

Depends on / 依赖: lt_irrefl
-/
@[simp] lemma toMeasure_mk (μ : Measure Ω) (h : IsFiniteMeasure μ) :
    FiniteMeasure.toMeasure (⟨μ, h⟩ : FiniteMeasure Ω) = μ := rfl

/--
lemma `measureReal_eq_coe_coeFn` / 引理 `measureReal_eq_coe_coeFn`

English:
lemma measureReal_eq_coe_coeFn
  given: {μ : FiniteMeasure Ω} {s : Set Ω}
  proof: rfl

@[simp]

中文:
引理 measure实数_eq_coe_coeFn
  条件: {μ : 有限测度 Ω} {s : 集合 Ω}
  证明: rfl

@[simp]

Depends on / 依赖: Lex.isStrictOrder, isStrictOrder
-/
@[simp] lemma measureReal_eq_coe_coeFn {μ : FiniteMeasure Ω} {s : Set Ω} :
    (μ : Measure Ω).real s = μ s := rfl

@[simp]
/--
theorem `ennreal_coeFn_eq_coeFn_toMeasure` / 定理 `ennreal_coeFn_eq_coeFn_toMeasure`

English:
theorem ennreal_coeFn_eq_coeFn_toMeasure
  given: (ν : FiniteMeasure Ω) (s : Set Ω)
  proof: ENNReal.coe_toNNReal (measure_lt_top (↑ν) s).ne

@[simp]

中文:
定理 ennreal_coeFn_eq_coeFn_toMeasure
  条件: (ν : 有限测度 Ω) (s : 集合 Ω)
  证明: ENNReal.coe_toNNReal (measure_lt_top (↑ν) s).ne

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, coe_toNNReal, measure_lt_top
-/
theorem ennreal_coeFn_eq_coeFn_toMeasure (ν : FiniteMeasure Ω) (s : Set Ω) :
    (ν s : Real>=0∞) = (ν : Measure Ω) s :=
  ENNReal.coe_toNNReal (measure_lt_top (↑ν) s).ne

@[simp]
/--
theorem `null_iff_toMeasure_null` / 定理 `null_iff_toMeasure_null`

English:
theorem null_iff_toMeasure_null
  given: (ν : FiniteMeasure Ω) (s : Set Ω)
  proof: ⟨fun h => by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h => congrArg ENNReal.toNNReal h⟩

@[mono, gcongr]

中文:
定理 null_iff_toMeasure_null
  条件: (ν : 有限测度 Ω) (s : 集合 Ω)
  证明: ⟨fun h => by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h => congrArg ENNReal.toNNReal h⟩

@[mono, gcongr]

Depends on / 依赖: ENNReal, ENNReal.coe_zero, ENNReal.toNNReal, coe_zero, ennreal_coeFn_eq_coeFn_toMeasure, toNNReal
-/
theorem null_iff_toMeasure_null (ν : FiniteMeasure Ω) (s : Set Ω) :
    ν s = 0 ↔ (ν : Measure Ω) s = 0 :=
  ⟨fun h => by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h => congrArg ENNReal.toNNReal h⟩

@[mono, gcongr]
/--
theorem `apply_mono` / 定理 `apply_mono`

English:
theorem apply_mono
  given: (μ : FiniteMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂)
  statement: μ s₁ <= μ s₂
  proof: ENNReal.toNNReal_mono (measure_ne_top _ s₂) ((μ : Measure Ω).mono h)

中文:
定理 apply_mono
  条件: (μ : 有限测度 Ω) {s₁ s₂ : 集合 Ω} (h : s₁ subseteq s₂)
  结论: μ s₁ <= μ s₂
  证明: ENNReal.toNNReal_mono (measure_ne_top _ s₂) ((μ : Measure Ω).mono h)

Depends on / 依赖: Classical, Classical.decRel, ENNReal, ENNReal.toNNReal_mono, IsWellFounded, IsWellFounded.wf, Measure, decRel, linearOrderOfSTO, measure_ne_top, toNNReal_mono, trichotomous, trichotomous_lex
-/
theorem apply_mono (μ : FiniteMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ subseteq s₂) : μ s₁ <= μ s₂ :=
  ENNReal.toNNReal_mono (measure_ne_top _ s₂) ((μ : Measure Ω).mono h)

/--
theorem `apply_union_le` / 定理 `apply_union_le`

English:
theorem apply_union_le
  given: (μ : FiniteMeasure Ω) {s₁ s₂ : Set Ω}
  statement: μ (s₁ union s₂) <= μ s₁ + μ s₂
  proof: by
  have := measure_union_le (μ := (μ : Measure Ω)) s₁ s₂
  apply (ENNReal.toNNReal_mono (by finiteness) this).trans_eq
  rw [ENNReal.toNNReal_add (by finiteness) (by finiteness)]; rw [coeFn_def]

中文:
定理 apply_union_le
  条件: (μ : 有限测度 Ω) {s₁ s₂ : 集合 Ω}
  结论: μ (s₁ union s₂) <= μ s₁ + μ s₂
  证明: by
  have := measure_union_le (μ := (μ : Measure Ω)) s₁ s₂
  apply (ENNReal.toNNReal_mono (by finiteness) this).trans_eq
  rw [ENNReal.toNNReal_add (by finiteness) (by finiteness)]; rw [coeFn_def]

Depends on / 依赖: ENNReal, ENNReal.toNNReal_add, ENNReal.toNNReal_mono, Lex.linearOrder, Measure, coeFn_def, finiteness, linearOrder, measure_union_le, toNNReal_add, toNNReal_mono, trans_eq
-/
theorem apply_union_le (μ : FiniteMeasure Ω) {s₁ s₂ : Set Ω} : μ (s₁ union s₂) <= μ s₁ + μ s₂ := by
  have := measure_union_le (μ := (μ : Measure Ω)) s₁ s₂
  apply (ENNReal.toNNReal_mono (by finiteness) this).trans_eq
  rw [ENNReal.toNNReal_add (by finiteness) (by finiteness)]; rw [coeFn_def]

/--
theorem `mono_null` / 定理 `mono_null`

English:
theorem mono_null
  given: (μ : FiniteMeasure Ω) (h : s subseteq t) (ht : μ t = 0)
  statement: μ s = 0
  proof: eq_bot_mono (apply_mono μ h) ht

中文:
定理 mono_null
  条件: (μ : 有限测度 Ω) (h : s subseteq t) (ht : μ t = 0)
  结论: μ s = 0
  证明: eq_bot_mono (apply_mono μ h) ht

Depends on / 依赖: apply_mono, eq_bot_mono
-/
theorem mono_null (μ : FiniteMeasure Ω) (h : s subseteq t) (ht : μ t = 0) : μ s = 0 :=
  eq_bot_mono (apply_mono μ h) ht

/--
lemma `pos_mono` / 引理 `pos_mono`

English:
lemma pos_mono
  given: (μ : FiniteMeasure Ω) (h : s subseteq t) (hs : 0 < μ s)
  proof: hs.trans_le μ.apply_mono h

中文:
引理 pos_mono
  条件: (μ : 有限测度 Ω) (h : s subseteq t) (hs : 0 < μ s)
  证明: hs.trans_le μ.apply_mono h

Depends on / 依赖: apply_mono, hs.trans_le, trans_le
-/
lemma pos_mono (μ : FiniteMeasure Ω) (h : s subseteq t) (hs : 0 < μ s) :
0 < μ t := hs.trans_le μ.apply_mono h

/--
lemma `tendsto_measure_iUnion_accumulate` / 引理 `tendsto_measure_iUnion_accumulate`

English:
lemma tendsto_measure_iUnion_accumulate
  statement: {ι : Type*} [Preorder ι]
  proof: by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure) (ι := ι)

中文:
引理 tendsto_measure_iUnion_accumulate
  结论: {ι : 类型} [预序 ι]
  证明: by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure) (ι := ι)
-/
protected lemma tendsto_measure_iUnion_accumulate {ι : Type*} [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {μ : FiniteMeasure Ω} {f : ι -> Set Ω} :
    Tendsto (fun i => μ (accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure) (ι := ι)

/--
Definition of `mass` / `mass` 的定义

English:
definition mass
  signature: (μ : FiniteMeasure Ω)
  body: μ univ

中文:
定义 mass
  签名: (μ : 有限测度 Ω)
  定义体: μ univ
-/
def mass (μ : FiniteMeasure Ω) : Real>=0 := μ univ

/--
theorem `apply_le_mass` / 定理 `apply_le_mass`

English:
theorem apply_le_mass
  given: (μ : FiniteMeasure Ω) (s : Set Ω)
  statement: μ s <= μ.mass
  proof: by
  simpa using! apply_mono μ (subset_univ s)

@[simp]

中文:
定理 apply_le_mass
  条件: (μ : 有限测度 Ω) (s : 集合 Ω)
  结论: μ s <= μ.mass
  证明: by
  simpa using! apply_mono μ (subset_univ s)

@[simp]
-/
@[simp] theorem apply_le_mass (μ : FiniteMeasure Ω) (s : Set Ω) : μ s <= μ.mass := by
  simpa using! apply_mono μ (subset_univ s)

@[simp]
/--
theorem `ennreal_mass` / 定理 `ennreal_mass`

English:
theorem ennreal_mass
  given: {μ : FiniteMeasure Ω}
  statement: (μ.mass : Real>=0∞) = (μ : Measure Ω) univ
  proof: ennreal_coeFn_eq_coeFn_toMeasure μ Set.univ

中文:
定理 ennreal_mass
  条件: {μ : 有限测度 Ω}
  结论: (μ.mass : 实数>=0∞) = (μ : 测度 Ω) univ
  证明: ennreal_coeFn_eq_coeFn_toMeasure μ Set.univ

Depends on / 依赖: Set.univ, ennreal_coeFn_eq_coeFn_toMeasure
-/
theorem ennreal_mass {μ : FiniteMeasure Ω} : (μ.mass : Real>=0∞) = (μ : Measure Ω) univ :=
  ennreal_coeFn_eq_coeFn_toMeasure μ Set.univ

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (FiniteMeasure Ω) where zero
  body: ⟨0, MeasureTheory.isFiniteMeasureZero⟩

中文:
实例 instZero
  签名: : 零 (有限测度 Ω) where zero
  定义体: ⟨0, MeasureTheory.isFiniteMeasureZero⟩

Depends on / 依赖: MeasureTheory, MeasureTheory.isFiniteMeasureZero, isFiniteMeasureZero
-/
instance instZero : Zero (FiniteMeasure Ω) where zero := ⟨0, MeasureTheory.isFiniteMeasureZero⟩

/--
lemma `coeFn_zero` / 引理 `coeFn_zero`

English:
lemma coeFn_zero
  statement: ⇑(0 : FiniteMeasure Ω) = 0
  proof: rfl

@[simp]

中文:
引理 coeFn_zero
  结论: ⇑(0 : 有限测度 Ω) = 0
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma coeFn_zero : ⇑(0 : FiniteMeasure Ω) = 0 := rfl

@[simp]
/--
theorem `zero_mass` / 定理 `zero_mass`

English:
theorem zero_mass
  statement: (0 : FiniteMeasure Ω).mass = 0
  proof: rfl

@[simp]

中文:
定理 zero_mass
  结论: (0 : 有限测度 Ω).mass = 0
  证明: rfl

@[simp]
-/
theorem zero_mass : (0 : FiniteMeasure Ω).mass = 0 := rfl

@[simp]
/--
theorem `mass_zero_iff` / 定理 `mass_zero_iff`

English:
theorem mass_zero_iff
  given: (μ : FiniteMeasure Ω)
  statement: μ.mass = 0 ↔ μ = 0
  proof: by
  refine ⟨fun μ_mass => ?_, fun hμ => by simp only [hμ, zero_mass]⟩
  apply toMeasure_injective
  apply Measure.measure_univ_eq_zero.mp
  rwa [← ennreal_mass, ENNReal.coe_eq_zero]

中文:
定理 mass_zero_iff
  条件: (μ : 有限测度 Ω)
  结论: μ.mass = 0 ↔ μ = 0
  证明: by
  refine ⟨fun μ_mass => ?_, fun hμ => by simp only [hμ, zero_mass]⟩
  apply toMeasure_injective
  apply Measure.measure_univ_eq_zero.mp
  rwa [← ennreal_mass, ENNReal.coe_eq_zero]

Depends on / 依赖: ENNReal, ENNReal.coe_eq_zero, Measure, Measure.measure_univ_eq_zero.mp, coe_eq_zero, ennreal_mass, measure_univ_eq_zero, toMeasure_injective, zero_mass
-/
theorem mass_zero_iff (μ : FiniteMeasure Ω) : μ.mass = 0 ↔ μ = 0 := by
  refine ⟨fun μ_mass => ?_, fun hμ => by simp only [hμ, zero_mass]⟩
  apply toMeasure_injective
  apply Measure.measure_univ_eq_zero.mp
  rwa [← ennreal_mass, ENNReal.coe_eq_zero]

/--
theorem `mass_nonzero_iff` / 定理 `mass_nonzero_iff`

English:
theorem mass_nonzero_iff
  given: (μ : FiniteMeasure Ω)
  statement: μ.mass != 0 ↔ μ != 0
  proof: not_iff_not.mpr FiniteMeasure.mass_zero_iff μ

@[ext]

中文:
定理 mass_nonzero_iff
  条件: (μ : 有限测度 Ω)
  结论: μ.mass != 0 ↔ μ != 0
  证明: not_iff_not.mpr FiniteMeasure.mass_zero_iff μ

@[ext]

Depends on / 依赖: FiniteMeasure, FiniteMeasure.mass_zero_iff, mass_zero_iff, not_iff_not, not_iff_not.mpr
-/
theorem mass_nonzero_iff (μ : FiniteMeasure Ω) : μ.mass != 0 ↔ μ != 0 :=
not_iff_not.mpr FiniteMeasure.mass_zero_iff μ

@[ext]
/--
theorem `eq_of_forall_toMeasure_apply_eq` / 定理 `eq_of_forall_toMeasure_apply_eq`

English:
theorem eq_of_forall_toMeasure_apply_eq
  statement: (μ ν : FiniteMeasure Ω)
  proof: by
  apply Subtype.ext
  ext1 s s_mble
  exact h s s_mble

中文:
定理 eq_of_对任意_toMeasure_apply_eq
  结论: (μ ν : 有限测度 Ω)
  证明: by
  apply Subtype.ext
  ext1 s s_mble
  exact h s s_mble

Depends on / 依赖: Subtype, Subtype.ext, s_mble
-/
theorem eq_of_forall_toMeasure_apply_eq (μ ν : FiniteMeasure Ω)
    (h : forall s : Set Ω, MeasurableSet s -> (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν := by
  apply Subtype.ext
  ext1 s s_mble
  exact h s s_mble

/--
theorem `eq_of_forall_apply_eq` / 定理 `eq_of_forall_apply_eq`

English:
theorem eq_of_forall_apply_eq
  statement: (μ ν : FiniteMeasure Ω)
  proof: by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : Real>=0 -> Real>=0∞) (h s s_mble)

中文:
定理 eq_of_对任意_apply_eq
  结论: (μ ν : 有限测度 Ω)
  证明: by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : Real>=0 -> Real>=0∞) (h s s_mble)

Depends on / 依赖: congr_arg, ennreal_coeFn_eq_coeFn_toMeasure, s_mble
-/
theorem eq_of_forall_apply_eq (μ ν : FiniteMeasure Ω)
    (h : forall s : Set Ω, MeasurableSet s -> μ s = ν s) : μ = ν := by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : Real>=0 -> Real>=0∞) (h s s_mble)

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (FiniteMeasure Ω)
  body: ⟨0⟩

中文:
实例 instInhabited
  签名: : 可居 (有限测度 Ω)
  定义体: ⟨0⟩
-/
instance instInhabited : Inhabited (FiniteMeasure Ω) := ⟨0⟩

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (FiniteMeasure Ω) where add μ ν
  body: ⟨μ + ν, MeasureTheory.isFiniteMeasureAdd⟩

中文:
实例 instAdd
  签名: : 加法 (有限测度 Ω) where add μ ν
  定义体: ⟨μ + ν, MeasureTheory.isFiniteMeasureAdd⟩

Depends on / 依赖: MeasureTheory, MeasureTheory.isFiniteMeasureAdd, isFiniteMeasureAdd
-/
instance instAdd : Add (FiniteMeasure Ω) where add μ ν := ⟨μ + ν, MeasureTheory.isFiniteMeasureAdd⟩

variable {R : Type*} [SMul R Real>=0] [SMul R Real>=0∞] [IsScalarTower R Real>=0 Real>=0∞]
  [IsScalarTower R Real>=0∞ Real>=0∞]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul R (FiniteMeasure Ω) where
  body: ⟨c • (μ : Measure Ω), MeasureTheory.isFiniteMeasureSMulOfNNRealTower⟩

@[simp, norm_cast]

中文:
实例 instSMul
  签名: : 标量乘法 R (有限测度 Ω) where
  定义体: ⟨c • (μ : Measure Ω), MeasureTheory.isFiniteMeasureSMulOfNNRealTower⟩

@[simp, norm_cast]

Depends on / 依赖: Measure, MeasureTheory, MeasureTheory.isFiniteMeasureSMulOfNNRealTower, isFiniteMeasureSMulOfNNRealTower
-/
instance instSMul : SMul R (FiniteMeasure Ω) where
  smul (c : R) μ := ⟨c • (μ : Measure Ω), MeasureTheory.isFiniteMeasureSMulOfNNRealTower⟩

@[simp, norm_cast]
/--
theorem `toMeasure_zero` / 定理 `toMeasure_zero`

English:
theorem toMeasure_zero
  statement: ((↑) : FiniteMeasure Ω -> Measure Ω) 0 = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 toMeasure_zero
  结论: ((↑) : 有限测度 Ω -> 测度 Ω) 0 = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem toMeasure_zero : ((↑) : FiniteMeasure Ω -> Measure Ω) 0 = 0 := rfl

@[simp, norm_cast]
/--
theorem `toMeasure_add` / 定理 `toMeasure_add`

English:
theorem toMeasure_add
  given: (μ ν : FiniteMeasure Ω)
  statement: ↑(μ + ν) = (↑μ + ↑ν : Measure Ω)
  proof: rfl

@[simp, norm_cast]

中文:
定理 toMeasure_add
  条件: (μ ν : 有限测度 Ω)
  结论: ↑(μ + ν) = (↑μ + ↑ν : 测度 Ω)
  证明: rfl

@[simp, norm_cast]
-/
theorem toMeasure_add (μ ν : FiniteMeasure Ω) : ↑(μ + ν) = (↑μ + ↑ν : Measure Ω) := rfl

@[simp, norm_cast]
/--
theorem `toMeasure_smul` / 定理 `toMeasure_smul`

English:
theorem toMeasure_smul
  given: (c : R) (μ : FiniteMeasure Ω)
  statement: ↑(c • μ) = c • (μ : Measure Ω)
  proof: rfl

@[simp, norm_cast]

中文:
定理 toMeasure_smul
  条件: (c : R) (μ : 有限测度 Ω)
  结论: ↑(c • μ) = c • (μ : 测度 Ω)
  证明: rfl

@[simp, norm_cast]
-/
theorem toMeasure_smul (c : R) (μ : FiniteMeasure Ω) : ↑(c • μ) = c • (μ : Measure Ω) :=
  rfl

@[simp, norm_cast]
/--
theorem `coeFn_add` / 定理 `coeFn_add`

English:
theorem coeFn_add
  given: (μ ν : FiniteMeasure Ω)
  statement: (⇑(μ + ν) : Set Ω -> Real>=0) = (⇑μ + ⇑ν : Set Ω -> Real>=0)
  proof: by
  funext
  simp only [Pi.add_apply, ← ENNReal.coe_inj, ennreal_coeFn_eq_coeFn_toMeasure,
    ENNReal.coe_add]
  norm_cast

@[simp, norm_cast]

中文:
定理 coeFn_add
  条件: (μ ν : 有限测度 Ω)
  结论: (⇑(μ + ν) : 集合 Ω -> 实数>=0) = (⇑μ + ⇑ν : 集合 Ω -> 实数>=0)
  证明: by
  funext
  simp only [Pi.add_apply, ← ENNReal.coe_inj, ennreal_coeFn_eq_coeFn_toMeasure,
    ENNReal.coe_add]
  norm_cast

@[simp, norm_cast]

Depends on / 依赖: ENNReal, ENNReal.coe_add, ENNReal.coe_inj, Pi.add_apply, add_apply, coe_add, coe_inj, ennreal_coeFn_eq_coeFn_toMeasure
-/
theorem coeFn_add (μ ν : FiniteMeasure Ω) : (⇑(μ + ν) : Set Ω -> Real>=0) = (⇑μ + ⇑ν : Set Ω -> Real>=0) := by
  funext
  simp only [Pi.add_apply, ← ENNReal.coe_inj, ennreal_coeFn_eq_coeFn_toMeasure,
    ENNReal.coe_add]
  norm_cast

@[simp, norm_cast]
/--
theorem `coeFn_smul` / 定理 `coeFn_smul`

English:
theorem coeFn_smul
  given: [IsScalarTower R Real>=0 Real>=0] (c : R) (μ : FiniteMeasure Ω)
  proof: by
  funext; simp [← ENNReal.coe_inj, ENNReal.coe_smul]

中文:
定理 coeFn_smul
  条件: [标量塔 R 实数>=0 实数>=0] (c : R) (μ : 有限测度 Ω)
  证明: by
  funext; simp [← ENNReal.coe_inj, ENNReal.coe_smul]

Depends on / 依赖: ENNReal, ENNReal.coe_inj, ENNReal.coe_smul, coe_inj, coe_smul
-/
theorem coeFn_smul [IsScalarTower R Real>=0 Real>=0] (c : R) (μ : FiniteMeasure Ω) :
    (⇑(c • μ) : Set Ω -> Real>=0) = c • (⇑μ : Set Ω -> Real>=0) := by
  funext; simp [← ENNReal.coe_inj, ENNReal.coe_smul]

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (FiniteMeasure Ω)
  body: fast_instance%
  toMeasure_injective.addCommMonoid _ toMeasure_zero toMeasure_add fun _ _ => toMeasure_smul _ _

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 (有限测度 Ω)
  定义体: fast_instance%
  toMeasure_injective.addCommMonoid _ toMeasure_zero toMeasure_add fun _ _ => toMeasure_smul _ _

Depends on / 依赖: fast_instance
-/
instance instAddCommMonoid : AddCommMonoid (FiniteMeasure Ω) := fast_instance%
  toMeasure_injective.addCommMonoid _ toMeasure_zero toMeasure_add fun _ _ => toMeasure_smul _ _

/-- Coercion is an `AddMonoidHom`. -/
@[simps]
/--
Definition of `toMeasureAddMonoidHom` / `toMeasureAddMonoidHom` 的定义

English:
definition toMeasureAddMonoidHom
  signature: : FiniteMeasure Ω ->+ Measure Ω where
  body: (↑)
  map_zero' := toMeasure_zero
  map_add' := toMeasure_add

@[simp, norm_cast]

中文:
定义 toMeasureAddMonoidHom
  签名: : 有限测度 Ω ->+ 测度 Ω where
  定义体: (↑)
  map_zero' := toMeasure_zero
  map_add' := toMeasure_add

@[simp, norm_cast]
-/
def toMeasureAddMonoidHom : FiniteMeasure Ω ->+ Measure Ω where
  toFun := (↑)
  map_zero' := toMeasure_zero
  map_add' := toMeasure_add

@[simp, norm_cast]
/--
theorem `toMeasure_sum` / 定理 `toMeasure_sum`

English:
theorem toMeasure_sum
  given: {ι : Type*} {s : Finset ι} {ν : ι -> FiniteMeasure Ω}
  proof: map_sum toMeasureAddMonoidHom _ _

中文:
定理 toMeasure_sum
  条件: {ι : 类型} {s : 有限集 ι} {ν : ι -> 有限测度 Ω}
  证明: map_sum toMeasureAddMonoidHom _ _

Depends on / 依赖: map_sum, toMeasureAddMonoidHom
-/
theorem toMeasure_sum {ι : Type*} {s : Finset ι} {ν : ι -> FiniteMeasure Ω} :
    ↑(∑ i in s, ν i) = ∑ i in s, (ν i : Measure Ω) :=
  map_sum toMeasureAddMonoidHom _ _

instance {Ω : Type*} [MeasurableSpace Ω] : Module Real>=0 (FiniteMeasure Ω) :=
  Function.Injective.module _ toMeasureAddMonoidHom toMeasure_injective toMeasure_smul

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [IsScalarTower R Real>=0 Real>=0] (c : R) (μ : FiniteMeasure Ω) (s : Set Ω)
  proof: by
  rw [coeFn_smul]; rw [Pi.smul_apply]

中文:
定理 smul_apply
  条件: [标量塔 R 实数>=0 实数>=0] (c : R) (μ : 有限测度 Ω) (s : 集合 Ω)
  证明: by
  rw [coeFn_smul]; rw [Pi.smul_apply]

Depends on / 依赖: Pi.smul_apply, coeFn_smul, smul_apply
-/
theorem smul_apply [IsScalarTower R Real>=0 Real>=0] (c : R) (μ : FiniteMeasure Ω) (s : Set Ω) :
    (c • μ) s = c • μ s := by
  rw [coeFn_smul]; rw [Pi.smul_apply]

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (μ : FiniteMeasure Ω) (A : Set Ω)
  body: (μ : Measure Ω).restrict A
  property := MeasureTheory.isFiniteMeasureRestrict (μ : Measure Ω) A

@[simp]

中文:
定义 restrict
  签名: (μ : 有限测度 Ω) (A : 集合 Ω)
  定义体: (μ : Measure Ω).restrict A
  property := MeasureTheory.isFiniteMeasureRestrict (μ : Measure Ω) A

@[simp]

Depends on / 依赖: Measure, restrict
-/
def restrict (μ : FiniteMeasure Ω) (A : Set Ω) : FiniteMeasure Ω where
  val := (μ : Measure Ω).restrict A
  property := MeasureTheory.isFiniteMeasureRestrict (μ : Measure Ω) A

@[simp]
/--
theorem `restrict_measure_eq` / 定理 `restrict_measure_eq`

English:
theorem restrict_measure_eq
  given: (μ : FiniteMeasure Ω) (A : Set Ω)
  proof: rfl

中文:
定理 restrict_measure_eq
  条件: (μ : 有限测度 Ω) (A : 集合 Ω)
  证明: rfl
-/
theorem restrict_measure_eq (μ : FiniteMeasure Ω) (A : Set Ω) :
    (μ.restrict A : Measure Ω) = (μ : Measure Ω).restrict A := rfl

/--
theorem `restrict_apply_measure` / 定理 `restrict_apply_measure`

English:
theorem restrict_apply_measure
  statement: (μ : FiniteMeasure Ω) (A : Set Ω) {s : Set Ω}
  proof: Measure.restrict_apply s_mble

@[simp]

中文:
定理 restrict_apply_measure
  结论: (μ : 有限测度 Ω) (A : 集合 Ω) {s : 集合 Ω}
  证明: Measure.restrict_apply s_mble

@[simp]

Depends on / 依赖: Measure, Measure.restrict_apply, restrict_apply, s_mble
-/
theorem restrict_apply_measure (μ : FiniteMeasure Ω) (A : Set Ω) {s : Set Ω}
    (s_mble : MeasurableSet s) : (μ.restrict A : Measure Ω) s = (μ : Measure Ω) (s inter A) :=
  Measure.restrict_apply s_mble

@[simp]
/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  given: (μ : FiniteMeasure Ω) (A : Set Ω) {s : Set Ω} (s_mble : MeasurableSet s)
  proof: by
  apply congr_arg ENNReal.toNNReal
  exact Measure.restrict_apply s_mble

@[simp]

中文:
定理 restrict_apply
  条件: (μ : 有限测度 Ω) (A : 集合 Ω) {s : 集合 Ω} (s_mble : 可测集 s)
  证明: by
  apply congr_arg ENNReal.toNNReal
  exact Measure.restrict_apply s_mble

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toNNReal, Measure, Measure.restrict_apply, congr_arg, restrict_apply, s_mble, toNNReal
-/
theorem restrict_apply (μ : FiniteMeasure Ω) (A : Set Ω) {s : Set Ω} (s_mble : MeasurableSet s) :
    (μ.restrict A) s = μ (s inter A) := by
  apply congr_arg ENNReal.toNNReal
  exact Measure.restrict_apply s_mble

@[simp]
/--
theorem `restrict_mass` / 定理 `restrict_mass`

English:
theorem restrict_mass
  given: (μ : FiniteMeasure Ω) (A : Set Ω)
  statement: (μ.restrict A).mass = μ A
  proof: by
  simp only [mass, restrict_apply μ A MeasurableSet.univ, univ_inter]

中文:
定理 restrict_mass
  条件: (μ : 有限测度 Ω) (A : 集合 Ω)
  结论: (μ.restrict A).mass = μ A
  证明: by
  simp only [mass, restrict_apply μ A MeasurableSet.univ, univ_inter]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, restrict_apply, univ_inter
-/
theorem restrict_mass (μ : FiniteMeasure Ω) (A : Set Ω) : (μ.restrict A).mass = μ A := by
  simp only [mass, restrict_apply μ A MeasurableSet.univ, univ_inter]

/--
lemma `restrict_univ` / 引理 `restrict_univ`

English:
lemma restrict_univ
  given: {μ : FiniteMeasure Ω}
  statement: μ.restrict univ = μ
  proof: by
  ext; simp

中文:
引理 restrict_univ
  条件: {μ : 有限测度 Ω}
  结论: μ.restrict univ = μ
  证明: by
  ext; simp
-/
@[simp] lemma restrict_univ {μ : FiniteMeasure Ω} : μ.restrict univ = μ := by
  ext; simp

/--
lemma `restrict_union` / 引理 `restrict_union`

English:
lemma restrict_union
  given: {μ : FiniteMeasure Ω} {s t : Set Ω} (h : Disjoint s t) (ht : MeasurableSet t)
  proof: by
  ext u hu
  simp [Measure.restrict_union h ht]

中文:
引理 restrict_union
  条件: {μ : 有限测度 Ω} {s t : 集合 Ω} (h : Disjoint s t) (ht : 可测集 t)
  证明: by
  ext u hu
  simp [Measure.restrict_union h ht]

Depends on / 依赖: Measure, Measure.restrict_union, restrict_union
-/
lemma restrict_union {μ : FiniteMeasure Ω} {s t : Set Ω} (h : Disjoint s t) (ht : MeasurableSet t) :
    μ.restrict (s union t) = μ.restrict s + μ.restrict t := by
  ext u hu
  simp [Measure.restrict_union h ht]

/--
lemma `restrict_biUnion_finset` / 引理 `restrict_biUnion_finset`

English:
lemma restrict_biUnion_finset
  statement: {ι : Type*} {μ : FiniteMeasure Ω} {T : Finset ι}
  proof: by
  ext t ht
  simp only [restrict_measure_eq, toMeasure_sum, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Measure.restrict_biUnion_finset hd hm]
  simp only [Measure.sum_fintype, Finset.univ_eq_attach, Measure.coe_finsetSum, Finset.sum_apply]
  conv_rhs => rw [← Finset.sum_attach]

@[simp]

中文:
引理 restrict_biUnion_finset
  结论: {ι : 类型} {μ : 有限测度 Ω} {T : 有限集 ι}
  证明: by
  ext t ht
  simp only [restrict_measure_eq, toMeasure_sum, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Measure.restrict_biUnion_finset hd hm]
  simp only [Measure.sum_fintype, Finset.univ_eq_attach, Measure.coe_finsetSum, Finset.sum_apply]
  conv_rhs => rw [← Finset.sum_attach]

@[simp]

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_attach, Finset.univ_eq_attach, Measure, Measure.coe_finsetSum, Measure.restrict_biUnion_finset, Measure.sum_fintype, coe_finsetSum, conv_rhs, restrict_biUnion_finset, restrict_measure_eq, sum_apply, sum_attach, sum_fintype, toMeasure_sum, univ_eq_attach
-/
lemma restrict_biUnion_finset {ι : Type*} {μ : FiniteMeasure Ω} {T : Finset ι}
    {s : ι -> Set Ω} (hd : (T : Set ι).Pairwise (Disjoint on s)) (hm : forall i, MeasurableSet (s i)) :
    μ.restrict (⋃ i in T, s i) = ∑ i in T, μ.restrict (s i) := by
  ext t ht
  simp only [restrict_measure_eq, toMeasure_sum, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Measure.restrict_biUnion_finset hd hm]
  simp only [Measure.sum_fintype, Finset.univ_eq_attach, Measure.coe_finsetSum, Finset.sum_apply]
  conv_rhs => rw [← Finset.sum_attach]

@[simp]
/--
theorem `restrict_eq_zero_iff` / 定理 `restrict_eq_zero_iff`

English:
theorem restrict_eq_zero_iff
  given: (μ : FiniteMeasure Ω) (A : Set Ω)
  statement: μ.restrict A = 0 ↔ μ A = 0
  proof: by
  rw [← mass_zero_iff]; rw [restrict_mass]

中文:
定理 restrict_eq_zero_iff
  条件: (μ : 有限测度 Ω) (A : 集合 Ω)
  结论: μ.restrict A = 0 ↔ μ A = 0
  证明: by
  rw [← mass_zero_iff]; rw [restrict_mass]

Depends on / 依赖: mass_zero_iff, restrict_mass
-/
theorem restrict_eq_zero_iff (μ : FiniteMeasure Ω) (A : Set Ω) : μ.restrict A = 0 ↔ μ A = 0 := by
  rw [← mass_zero_iff]; rw [restrict_mass]

/--
theorem `restrict_nonzero_iff` / 定理 `restrict_nonzero_iff`

English:
theorem restrict_nonzero_iff
  given: (μ : FiniteMeasure Ω) (A : Set Ω)
  statement: μ.restrict A != 0 ↔ μ A != 0
  proof: by
  simp

中文:
定理 restrict_nonzero_iff
  条件: (μ : 有限测度 Ω) (A : 集合 Ω)
  结论: μ.restrict A != 0 ↔ μ A != 0
  证明: by
  simp
-/
theorem restrict_nonzero_iff (μ : FiniteMeasure Ω) (A : Set Ω) : μ.restrict A != 0 ↔ μ A != 0 := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MeasurableSpace (FiniteMeasure Ω)
  body: inferInstanceAs MeasurableSpace (Subtype _)

中文:
实例 :
  签名: 可测空间 (有限测度 Ω)
  定义体: inferInstanceAs MeasurableSpace (Subtype _)

Depends on / 依赖: MeasurableSpace, Subtype
-/
instance : MeasurableSpace (FiniteMeasure Ω) :=
inferInstanceAs MeasurableSpace (Subtype _)

/--
lemma `measurableSet_isFiniteMeasure` / 引理 `measurableSet_isFiniteMeasure`

English:
lemma measurableSet_isFiniteMeasure
  statement: MeasurableSet { μ : Measure Ω | IsFiniteMeasure μ }
  proof: by
  suffices { μ : Measure Ω | IsFiniteMeasure μ } = (fun μ => μ univ) ⁻¹' (Set.Ico 0 ∞) by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ measurableSet_Ico
  ext μ
  simp only [mem_ofPred_eq, mem_preimage, mem_Ico, zero_le, true_and]
  exact isFiniteMeasure_iff μ

中文:
引理 measurableSet_isFiniteMeasure
  结论: 可测集 { μ : 测度 Ω | 是有限测度 μ }
  证明: by
  suffices { μ : Measure Ω | IsFiniteMeasure μ } = (fun μ => μ univ) ⁻¹' (Set.Ico 0 ∞) by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ measurableSet_Ico
  ext μ
  simp only [mem_ofPred_eq, mem_preimage, mem_Ico, zero_le, true_and]
  exact isFiniteMeasure_iff μ

Depends on / 依赖: IsFiniteMeasure, MeasurableSet, MeasurableSet.univ, Measure, Measure.measurable_coe, Set.Ico, isFiniteMeasure_iff, measurableSet_Ico, measurable_coe, mem_Ico, mem_ofPred_eq, mem_preimage, true_and, zero_le
-/
lemma measurableSet_isFiniteMeasure : MeasurableSet { μ : Measure Ω | IsFiniteMeasure μ } := by
  suffices { μ : Measure Ω | IsFiniteMeasure μ } = (fun μ => μ univ) ⁻¹' (Set.Ico 0 ∞) by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ measurableSet_Ico
  ext μ
  simp only [mem_ofPred_eq, mem_preimage, mem_Ico, zero_le, true_and]
  exact isFiniteMeasure_iff μ

/--
theorem `measurable_fun_prod` / 定理 `measurable_fun_prod`

English:
theorem measurable_fun_prod
  given: {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  proof: by
  have Heval {u v} (Hu : MeasurableSet u) (Hv : MeasurableSet v) :
      Measurable fun a : (FiniteMeasure α × FiniteMeasure β) =>
      a.1.toMeasure u * a.2.toMeasure v :=
    Measurable.mul
      ((Measure.measurable_coe Hu).comp (measurable_subtype_coe.comp measurable_fst))
      ((Measure.measurable_coe Hv).comp (measurable_subtype_coe.comp measurable_snd))
  apply Measurable.measure_of_isPiSystem generateFrom_prod.symm isPiSystem_prod _
  · simp_rw [← Set.univ_prod_univ, Measure.prod_prod, Heval MeasurableSet.univ MeasurableSet.univ]
  simp only [mem_image2, mem_ofPred_eq, forall_exists_index, and_imp]
  intro _ _ Hu _ Hv Heq
  simp_rw [← Heq, Measure.prod_prod, Heval Hu Hv]

中文:
定理 measurable_fun_prod
  条件: {α β : 类型} [可测空间 α] [可测空间 β]
  证明: by
  have Heval {u v} (Hu : MeasurableSet u) (Hv : MeasurableSet v) :
      Measurable fun a : (FiniteMeasure α × FiniteMeasure β) =>
      a.1.toMeasure u * a.2.toMeasure v :=
    Measurable.mul
      ((Measure.measurable_coe Hu).comp (measurable_subtype_coe.comp measurable_fst))
      ((Measure.measurable_coe Hv).comp (measurable_subtype_coe.comp measurable_snd))
  apply Measurable.measure_of_isPiSystem generateFrom_prod.symm isPiSystem_prod _
  · simp_rw [← Set.univ_prod_univ, Measure.prod_prod, Heval MeasurableSet.univ MeasurableSet.univ]
  simp only [mem_image2, mem_ofPred_eq, forall_exists_index, and_imp]
  intro _ _ Hu _ Hv Heq
  simp_rw [← Heq, Measure.prod_prod, Heval Hu Hv]

Depends on / 依赖: FiniteMeasure, Measurable, Measurable.measure_of_isPiSystem, Measurable.mul, MeasurableSet, MeasurableSet.univ, Measure, Measure.measurable_coe, Measure.prod_prod, Set.univ_prod_univ, generateFrom_prod, generateFrom_prod.symm, isPiSystem_prod, measurable_coe, measurable_fst, measurable_snd, measurable_subtype_coe, measurable_subtype_coe.comp, measure_of_isPiSystem, prod_prod
-/
theorem measurable_fun_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (fun (μ : FiniteMeasure α × FiniteMeasure β)
      => μ.1.toMeasure.prod μ.2.toMeasure) := by
  have Heval {u v} (Hu : MeasurableSet u) (Hv : MeasurableSet v) :
      Measurable fun a : (FiniteMeasure α × FiniteMeasure β) =>
      a.1.toMeasure u * a.2.toMeasure v :=
    Measurable.mul
      ((Measure.measurable_coe Hu).comp (measurable_subtype_coe.comp measurable_fst))
      ((Measure.measurable_coe Hv).comp (measurable_subtype_coe.comp measurable_snd))
  apply Measurable.measure_of_isPiSystem generateFrom_prod.symm isPiSystem_prod _
  · simp_rw [← Set.univ_prod_univ, Measure.prod_prod, Heval MeasurableSet.univ MeasurableSet.univ]
  simp only [mem_image2, mem_ofPred_eq, forall_exists_index, and_imp]
  intro _ _ Hu _ Hv Heq
  simp_rw [← Heq, Measure.prod_prod, Heval Hu Hv]

/--
lemma `apply_iUnion_le` / 引理 `apply_iUnion_le`

English:
lemma apply_iUnion_le
  statement: {μ : FiniteMeasure Ω} {f : Nat -> Set Ω}
  proof: by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

中文:
引理 apply_iUnion_le
  结论: {μ : 有限测度 Ω} {f : 自然数 -> 集合 Ω}
  证明: by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_tsum, MeasureTheory, MeasureTheory.measure_iUnion_le, coe_le_coe, coe_tsum, measure_iUnion_le
-/
lemma apply_iUnion_le {μ : FiniteMeasure Ω} {f : Nat -> Set Ω}
    (hf : Summable fun n => μ (f n)) :
    μ (⋃ n, f n) <= ∑' n, μ (f n) := by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

variable [TopologicalSpace Ω]

/--
theorem `ext_of_forall_lintegral_eq` / 定理 `ext_of_forall_lintegral_eq`

English:
theorem ext_of_forall_lintegral_eq
  statement: [HasOuterApproxClosed Ω] [BorelSpace Ω]
  proof: by
  apply Subtype.ext
  change (μ : Measure Ω) = (ν : Measure Ω)
  exact ext_of_forall_lintegral_eq_of_IsFiniteMeasure h

中文:
定理 ext_of_对任意_lintegral_eq
  结论: [有OuterApproxClosed Ω] [Borel空间 Ω]
  证明: by
  apply Subtype.ext
  change (μ : Measure Ω) = (ν : Measure Ω)
  exact ext_of_forall_lintegral_eq_of_IsFiniteMeasure h

Depends on / 依赖: Measure, Subtype, Subtype.ext, ext_of_forall_lintegral_eq_of_IsFiniteMeasure
-/
theorem ext_of_forall_lintegral_eq [HasOuterApproxClosed Ω] [BorelSpace Ω]
    {μ ν : FiniteMeasure Ω} (h : forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) :
    μ = ν := by
  apply Subtype.ext
  change (μ : Measure Ω) = (ν : Measure Ω)
  exact ext_of_forall_lintegral_eq_of_IsFiniteMeasure h

/--
theorem `ext_of_forall_integral_eq` / 定理 `ext_of_forall_integral_eq`

English:
theorem ext_of_forall_integral_eq
  statement: [HasOuterApproxClosed Ω] [BorelSpace Ω]
  proof: by
  apply ext_of_forall_lintegral_eq
  intro f
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ f).ne
      (lintegral_lt_top_of_nnreal ν f).ne).mp
  rw [toReal_lintegral_coe_eq_integral f μ]; rw [toReal_lintegral_coe_eq_integral f ν]
  exact h ⟨⟨fun x => (f x).toReal, Continuous.comp' NNReal.continuous_coe f.continuous⟩,
      f.map_bounded'⟩

中文:
定理 ext_of_对任意_integral_eq
  结论: [有OuterApproxClosed Ω] [Borel空间 Ω]
  证明: by
  apply ext_of_forall_lintegral_eq
  intro f
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ f).ne
      (lintegral_lt_top_of_nnreal ν f).ne).mp
  rw [toReal_lintegral_coe_eq_integral f μ]; rw [toReal_lintegral_coe_eq_integral f ν]
  exact h ⟨⟨fun x => (f x).toReal, Continuous.comp' NNReal.continuous_coe f.continuous⟩,
      f.map_bounded'⟩

Depends on / 依赖: Continuous, Continuous.comp, ENNReal, ENNReal.toReal_eq_toReal_iff, I.lower, IsMaximal, IsMaximal.isPrime, IsMaximal.maximal_proper, IsPrime, NNReal, NNReal.continuous_coe, Set.eq_univ_iff_forall.mp, Set.univ, coe_sup_eq, continuous, continuous_coe, contrapose, eq_univ_iff_forall, ext_of_forall_lintegral_eq, f.continuous
-/
theorem ext_of_forall_integral_eq [HasOuterApproxClosed Ω] [BorelSpace Ω]
    {μ ν : FiniteMeasure Ω} (h : forall (f : Ω ->ᵇ Real), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  apply ext_of_forall_lintegral_eq
  intro f
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ f).ne
      (lintegral_lt_top_of_nnreal ν f).ne).mp
  rw [toReal_lintegral_coe_eq_integral f μ]; rw [toReal_lintegral_coe_eq_integral f ν]
  exact h ⟨⟨fun x => (f x).toReal, Continuous.comp' NNReal.continuous_coe f.continuous⟩,
      f.map_bounded'⟩

/--
Definition of `testAgainstNN` / `testAgainstNN` 的定义

English:
definition testAgainstNN
  signature: (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0)
  body: (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal

@[simp]

中文:
定义 testAgainstNN
  签名: (μ : 有限测度 Ω) (f : Ω ->ᵇ 实数>=0)
  定义体: (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal

@[simp]

Depends on / 依赖: Measure, toNNReal
-/
def testAgainstNN (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0) : Real>=0 :=
  (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal

@[simp]
/--
theorem `testAgainstNN_coe_eq` / 定理 `testAgainstNN_coe_eq`

English:
theorem testAgainstNN_coe_eq
  given: {μ : FiniteMeasure Ω} {f : Ω ->ᵇ Real>=0}
  proof: ENNReal.coe_toNNReal (f.lintegral_lt_top_of_nnreal _).ne

中文:
定理 testAgainstNN_coe_eq
  条件: {μ : 有限测度 Ω} {f : Ω ->ᵇ 实数>=0}
  证明: ENNReal.coe_toNNReal (f.lintegral_lt_top_of_nnreal _).ne

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, coe_toNNReal, f.lintegral_lt_top_of_nnreal, lintegral_lt_top_of_nnreal
-/
theorem testAgainstNN_coe_eq {μ : FiniteMeasure Ω} {f : Ω ->ᵇ Real>=0} :
    (μ.testAgainstNN f : Real>=0∞) = ∫⁻ ω, f ω ∂(μ : Measure Ω) :=
  ENNReal.coe_toNNReal (f.lintegral_lt_top_of_nnreal _).ne

/--
theorem `testAgainstNN_const` / 定理 `testAgainstNN_const`

English:
theorem testAgainstNN_const
  given: (μ : FiniteMeasure Ω) (c : Real>=0)
  proof: by
  simp [← ENNReal.coe_inj]

中文:
定理 testAgainstNN_const
  条件: (μ : 有限测度 Ω) (c : 实数>=0)
  证明: by
  simp [← ENNReal.coe_inj]

Depends on / 依赖: ENNReal, ENNReal.coe_inj, coe_inj
-/
theorem testAgainstNN_const (μ : FiniteMeasure Ω) (c : Real>=0) :
    μ.testAgainstNN (BoundedContinuousFunction.const Ω c) = c * μ.mass := by
  simp [← ENNReal.coe_inj]

/--
theorem `testAgainstNN_mono` / 定理 `testAgainstNN_mono`

English:
theorem testAgainstNN_mono
  given: (μ : FiniteMeasure Ω) {f g : Ω ->ᵇ Real>=0} (f_le_g : (f : Ω -> Real>=0) <= g)
  proof: by
  simp only [← ENNReal.coe_le_coe, testAgainstNN_coe_eq]
  gcongr
  apply f_le_g

@[simp]

中文:
定理 testAgainstNN_mono
  条件: (μ : 有限测度 Ω) {f g : Ω ->ᵇ 实数>=0} (f_le_g : (f : Ω -> 实数>=0) <= g)
  证明: by
  simp only [← ENNReal.coe_le_coe, testAgainstNN_coe_eq]
  gcongr
  apply f_le_g

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, coe_le_coe, f_le_g, testAgainstNN_coe_eq
-/
theorem testAgainstNN_mono (μ : FiniteMeasure Ω) {f g : Ω ->ᵇ Real>=0} (f_le_g : (f : Ω -> Real>=0) <= g) :
    μ.testAgainstNN f <= μ.testAgainstNN g := by
  simp only [← ENNReal.coe_le_coe, testAgainstNN_coe_eq]
  gcongr
  apply f_le_g

@[simp]
/--
theorem `testAgainstNN_zero` / 定理 `testAgainstNN_zero`

English:
theorem testAgainstNN_zero
  given: (μ : FiniteMeasure Ω)
  statement: μ.testAgainstNN 0 = 0
  proof: by
  simpa only [zero_mul] using! μ.testAgainstNN_const 0

@[simp]

中文:
定理 testAgainstNN_zero
  条件: (μ : 有限测度 Ω)
  结论: μ.testAgainstNN 0 = 0
  证明: by
  simpa only [zero_mul] using! μ.testAgainstNN_const 0

@[simp]

Depends on / 依赖: I.lower, IsMaximal, IsPrime, IsPrime.compl_mem_of_notMem, IsPrime.isMaximal, IsPrime.toIsProper, J.lower, Set.eq_univ_iff_forall, Set.exists_of_ssubset, compl_mem_of_notMem, eq_univ_iff_forall, exists_of_ssubset, hIJ.le, inf_le_right, isMaximal, isMaximal_iff, sup_inf_inf_compl, sup_mem, testAgainstNN_const, toIsProper
-/
theorem testAgainstNN_zero (μ : FiniteMeasure Ω) : μ.testAgainstNN 0 = 0 := by
  simpa only [zero_mul] using! μ.testAgainstNN_const 0

@[simp]
/--
theorem `testAgainstNN_one` / 定理 `testAgainstNN_one`

English:
theorem testAgainstNN_one
  given: (μ : FiniteMeasure Ω)
  statement: μ.testAgainstNN 1 = μ.mass
  proof: by
  simp only [testAgainstNN, coe_one, Pi.one_apply, ENNReal.coe_one, lintegral_one]
  rfl

@[simp]

中文:
定理 testAgainstNN_one
  条件: (μ : 有限测度 Ω)
  结论: μ.testAgainstNN 1 = μ.mass
  证明: by
  simp only [testAgainstNN, coe_one, Pi.one_apply, ENNReal.coe_one, lintegral_one]
  rfl

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_one, Pi.one_apply, coe_one, compl_ideal, h.compl_ideal.toIdeal, isCompl_I_F, isCompl_compl, isCompl_compl.symm, lintegral_one, one_apply, testAgainstNN, toIdeal
-/
theorem testAgainstNN_one (μ : FiniteMeasure Ω) : μ.testAgainstNN 1 = μ.mass := by
  simp only [testAgainstNN, coe_one, Pi.one_apply, ENNReal.coe_one, lintegral_one]
  rfl

@[simp]
/--
theorem `zero_testAgainstNN_apply` / 定理 `zero_testAgainstNN_apply`

English:
theorem zero_testAgainstNN_apply
  given: (f : Ω ->ᵇ Real>=0)
  statement: (0 : FiniteMeasure Ω).testAgainstNN f = 0
  proof: by
  simp only [testAgainstNN, toMeasure_zero, lintegral_zero_measure, ENNReal.toNNReal_zero]

中文:
定理 zero_testAgainstNN_apply
  条件: (f : Ω ->ᵇ 实数>=0)
  结论: (0 : 有限测度 Ω).testAgainstNN f = 0
  证明: by
  simp only [testAgainstNN, toMeasure_zero, lintegral_zero_measure, ENNReal.toNNReal_zero]

Depends on / 依赖: ENNReal, ENNReal.toNNReal_zero, lintegral_zero_measure, testAgainstNN, toMeasure_zero, toNNReal_zero
-/
theorem zero_testAgainstNN_apply (f : Ω ->ᵇ Real>=0) : (0 : FiniteMeasure Ω).testAgainstNN f = 0 := by
  simp only [testAgainstNN, toMeasure_zero, lintegral_zero_measure, ENNReal.toNNReal_zero]

/--
theorem `zero_testAgainstNN` / 定理 `zero_testAgainstNN`

English:
theorem zero_testAgainstNN
  statement: (0 : FiniteMeasure Ω).testAgainstNN = 0
  proof: by
  funext
  simp only [zero_testAgainstNN_apply, Pi.zero_apply]

@[simp]

中文:
定理 zero_testAgainstNN
  结论: (0 : 有限测度 Ω).testAgainstNN = 0
  证明: by
  funext
  simp only [zero_testAgainstNN_apply, Pi.zero_apply]

@[simp]

Depends on / 依赖: Pi.zero_apply, zero_apply, zero_testAgainstNN_apply
-/
theorem zero_testAgainstNN : (0 : FiniteMeasure Ω).testAgainstNN = 0 := by
  funext
  simp only [zero_testAgainstNN_apply, Pi.zero_apply]

@[simp]
/--
theorem `smul_testAgainstNN_apply` / 定理 `smul_testAgainstNN_apply`

English:
theorem smul_testAgainstNN_apply
  given: (c : Real>=0) (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0)
  proof: by
  simp only [testAgainstNN, toMeasure_smul, smul_eq_mul, ← ENNReal.smul_toNNReal, ENNReal.smul_def,
    lintegral_smul_measure]

中文:
定理 smul_testAgainstNN_apply
  条件: (c : 实数>=0) (μ : 有限测度 Ω) (f : Ω ->ᵇ 实数>=0)
  证明: by
  simp only [testAgainstNN, toMeasure_smul, smul_eq_mul, ← ENNReal.smul_toNNReal, ENNReal.smul_def,
    lintegral_smul_measure]

Depends on / 依赖: ENNReal, ENNReal.smul_def, ENNReal.smul_toNNReal, lintegral_smul_measure, smul_def, smul_eq_mul, smul_toNNReal, testAgainstNN, toMeasure_smul
-/
theorem smul_testAgainstNN_apply (c : Real>=0) (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0) :
    (c • μ).testAgainstNN f = c • μ.testAgainstNN f := by
  simp only [testAgainstNN, toMeasure_smul, smul_eq_mul, ← ENNReal.smul_toNNReal, ENNReal.smul_def,
    lintegral_smul_measure]

section weak_convergence

variable [OpensMeasurableSpace Ω]

/--
theorem `testAgainstNN_add` / 定理 `testAgainstNN_add`

English:
theorem testAgainstNN_add
  given: (μ : FiniteMeasure Ω) (f₁ f₂ : Ω ->ᵇ Real>=0)
  proof: by
  simp only [← ENNReal.coe_inj, BoundedContinuousFunction.coe_add, ENNReal.coe_add, Pi.add_apply,
    testAgainstNN_coe_eq]
  exact lintegral_add_left (BoundedContinuousFunction.measurable_coe_ennreal_comp _) _

中文:
定理 testAgainstNN_add
  条件: (μ : 有限测度 Ω) (f₁ f₂ : Ω ->ᵇ 实数>=0)
  证明: by
  simp only [← ENNReal.coe_inj, BoundedContinuousFunction.coe_add, ENNReal.coe_add, Pi.add_apply,
    testAgainstNN_coe_eq]
  exact lintegral_add_left (BoundedContinuousFunction.measurable_coe_ennreal_comp _) _

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.coe_add, BoundedContinuousFunction.measurable_coe_ennreal_comp, ENNReal, ENNReal.coe_add, ENNReal.coe_inj, Pi.add_apply, add_apply, coe_add, coe_inj, lintegral_add_left, measurable_coe_ennreal_comp, testAgainstNN_coe_eq
-/
theorem testAgainstNN_add (μ : FiniteMeasure Ω) (f₁ f₂ : Ω ->ᵇ Real>=0) :
    μ.testAgainstNN (f₁ + f₂) = μ.testAgainstNN f₁ + μ.testAgainstNN f₂ := by
  simp only [← ENNReal.coe_inj, BoundedContinuousFunction.coe_add, ENNReal.coe_add, Pi.add_apply,
    testAgainstNN_coe_eq]
  exact lintegral_add_left (BoundedContinuousFunction.measurable_coe_ennreal_comp _) _

/--
theorem `testAgainstNN_smul` / 定理 `testAgainstNN_smul`

English:
theorem testAgainstNN_smul
  statement: [IsScalarTower R Real>=0 Real>=0] [PseudoMetricSpace R] [Zero R]
  proof: by
  simp only [← ENNReal.coe_inj, BoundedContinuousFunction.coe_smul, testAgainstNN_coe_eq,
    ENNReal.coe_smul]
  simp_rw [← smul_one_smul Real>=0∞ c (f _ : Real>=0∞), ← smul_one_smul Real>=0∞ c (lintegral _ _ : Real>=0∞),
    smul_eq_mul]
  exact lintegral_const_mul (c • (1 : Real>=0∞)) f.measurable_coe_ennreal_comp

中文:
定理 testAgainstNN_smul
  结论: [标量塔 R 实数>=0 实数>=0] [伪度量空间 R] [零 R]
  证明: by
  simp only [← ENNReal.coe_inj, BoundedContinuousFunction.coe_smul, testAgainstNN_coe_eq,
    ENNReal.coe_smul]
  simp_rw [← smul_one_smul Real>=0∞ c (f _ : Real>=0∞), ← smul_one_smul Real>=0∞ c (lintegral _ _ : Real>=0∞),
    smul_eq_mul]
  exact lintegral_const_mul (c • (1 : Real>=0∞)) f.measurable_coe_ennreal_comp

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.coe_smul, ENNReal, ENNReal.coe_inj, ENNReal.coe_smul, coe_inj, coe_smul, f.measurable_coe_ennreal_comp, lintegral, lintegral_const_mul, measurable_coe_ennreal_comp, simp_rw, smul_eq_mul, smul_one_smul, testAgainstNN_coe_eq
-/
theorem testAgainstNN_smul [IsScalarTower R Real>=0 Real>=0] [PseudoMetricSpace R] [Zero R]
    [IsBoundedSMul R Real>=0] (μ : FiniteMeasure Ω) (c : R) (f : Ω ->ᵇ Real>=0) :
    μ.testAgainstNN (c • f) = c • μ.testAgainstNN f := by
  simp only [← ENNReal.coe_inj, BoundedContinuousFunction.coe_smul, testAgainstNN_coe_eq,
    ENNReal.coe_smul]
  simp_rw [← smul_one_smul Real>=0∞ c (f _ : Real>=0∞), ← smul_one_smul Real>=0∞ c (lintegral _ _ : Real>=0∞),
    smul_eq_mul]
  exact lintegral_const_mul (c • (1 : Real>=0∞)) f.measurable_coe_ennreal_comp

/--
theorem `testAgainstNN_lipschitz_estimate` / 定理 `testAgainstNN_lipschitz_estimate`

English:
theorem testAgainstNN_lipschitz_estimate
  given: (μ : FiniteMeasure Ω) (f g : Ω ->ᵇ Real>=0)
  proof: by
  simp only [← μ.testAgainstNN_const (nndist f g), ← testAgainstNN_add, ← ENNReal.coe_le_coe,
    BoundedContinuousFunction.coe_add, const_apply, ENNReal.coe_add, Pi.add_apply,
    coe_nnreal_ennreal_nndist, testAgainstNN_coe_eq]
  apply lintegral_mono
  have le_dist : forall ω, dist (f ω) (g ω) <= nndist f g := BoundedContinuousFunction.dist_coe_le_dist
  intro ω
  have le' : f ω <= g ω + nndist f g := by
    calc f ω
     _ <= g ω + nndist (f ω) (g ω) := NNReal.le_add_nndist (f ω) (g ω)
     _ <= g ω + nndist f g := (add_le_add_iff_left (g ω)).mpr (le_dist ω)
  have le : (f ω : Real>=0∞) <= (g ω : Real>=0∞) + nndist f g := by
    simpa only [← ENNReal.coe_add] using (by exact_mod_cast le')
  rwa [coe_nnreal_ennreal_nndist] at le

中文:
定理 testAgainstNN_lipschitz_estimate
  条件: (μ : 有限测度 Ω) (f g : Ω ->ᵇ 实数>=0)
  证明: by
  simp only [← μ.testAgainstNN_const (nndist f g), ← testAgainstNN_add, ← ENNReal.coe_le_coe,
    BoundedContinuousFunction.coe_add, const_apply, ENNReal.coe_add, Pi.add_apply,
    coe_nnreal_ennreal_nndist, testAgainstNN_coe_eq]
  apply lintegral_mono
  have le_dist : forall ω, dist (f ω) (g ω) <= nndist f g := BoundedContinuousFunction.dist_coe_le_dist
  intro ω
  have le' : f ω <= g ω + nndist f g := by
    calc f ω
     _ <= g ω + nndist (f ω) (g ω) := NNReal.le_add_nndist (f ω) (g ω)
     _ <= g ω + nndist f g := (add_le_add_iff_left (g ω)).mpr (le_dist ω)
  have le : (f ω : Real>=0∞) <= (g ω : Real>=0∞) + nndist f g := by
    simpa only [← ENNReal.coe_add] using (by exact_mod_cast le')
  rwa [coe_nnreal_ennreal_nndist] at le

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.coe_add, BoundedContinuousFunction.dist_coe_le_dist, ENNReal, ENNReal.coe_add, ENNReal.coe_le_coe, NNReal, NNReal.le_add_nndist, Pi.add_apply, add_, add_apply, coe_add, coe_le_coe, coe_nnreal_ennreal_nndist, const_apply, dist_coe_le_dist, le_add_nndist, le_dist, lintegral_mono, nndist
-/
theorem testAgainstNN_lipschitz_estimate (μ : FiniteMeasure Ω) (f g : Ω ->ᵇ Real>=0) :
    μ.testAgainstNN f <= μ.testAgainstNN g + nndist f g * μ.mass := by
  simp only [← μ.testAgainstNN_const (nndist f g), ← testAgainstNN_add, ← ENNReal.coe_le_coe,
    BoundedContinuousFunction.coe_add, const_apply, ENNReal.coe_add, Pi.add_apply,
    coe_nnreal_ennreal_nndist, testAgainstNN_coe_eq]
  apply lintegral_mono
  have le_dist : forall ω, dist (f ω) (g ω) <= nndist f g := BoundedContinuousFunction.dist_coe_le_dist
  intro ω
  have le' : f ω <= g ω + nndist f g := by
    calc f ω
     _ <= g ω + nndist (f ω) (g ω) := NNReal.le_add_nndist (f ω) (g ω)
     _ <= g ω + nndist f g := (add_le_add_iff_left (g ω)).mpr (le_dist ω)
  have le : (f ω : Real>=0∞) <= (g ω : Real>=0∞) + nndist f g := by
    simpa only [← ENNReal.coe_add] using (by exact_mod_cast le')
  rwa [coe_nnreal_ennreal_nndist] at le

/--
theorem `testAgainstNN_lipschitz` / 定理 `testAgainstNN_lipschitz`

English:
theorem testAgainstNN_lipschitz
  given: (μ : FiniteMeasure Ω)
  proof: by
  rw [lipschitzWith_iff_dist_le_mul]
  intro f₁ f₂
  suffices abs (μ.testAgainstNN f₁ - μ.testAgainstNN f₂ : Real) <= μ.mass * dist f₁ f₂ by
    rwa [NNReal.dist_eq]
  apply abs_le.mpr
  constructor
  · have key := μ.testAgainstNN_lipschitz_estimate f₂ f₁
    rw [mul_comm] at key
    suffices ↑(μ.testAgainstNN f₂) <= ↑(μ.testAgainstNN f₁) + ↑μ.mass * dist f₁ f₂ by linarith
    simpa [nndist_comm] using NNReal.coe_mono key
  · have key := μ.testAgainstNN_lipschitz_estimate f₁ f₂
    rw [mul_comm] at key
    suffices ↑(μ.testAgainstNN f₁) <= ↑(μ.testAgainstNN f₂) + ↑μ.mass * dist f₁ f₂ by linarith
    simpa using NNReal.coe_mono key

中文:
定理 testAgainstNN_lipschitz
  条件: (μ : 有限测度 Ω)
  证明: by
  rw [lipschitzWith_iff_dist_le_mul]
  intro f₁ f₂
  suffices abs (μ.testAgainstNN f₁ - μ.testAgainstNN f₂ : Real) <= μ.mass * dist f₁ f₂ by
    rwa [NNReal.dist_eq]
  apply abs_le.mpr
  constructor
  · have key := μ.testAgainstNN_lipschitz_estimate f₂ f₁
    rw [mul_comm] at key
    suffices ↑(μ.testAgainstNN f₂) <= ↑(μ.testAgainstNN f₁) + ↑μ.mass * dist f₁ f₂ by linarith
    simpa [nndist_comm] using NNReal.coe_mono key
  · have key := μ.testAgainstNN_lipschitz_estimate f₁ f₂
    rw [mul_comm] at key
    suffices ↑(μ.testAgainstNN f₁) <= ↑(μ.testAgainstNN f₂) + ↑μ.mass * dist f₁ f₂ by linarith
    simpa using NNReal.coe_mono key

Depends on / 依赖: NNReal, NNReal.coe_mono, NNReal.dist_eq, abs_le, abs_le.mpr, coe_mono, dist_eq, lipschitzWith_iff_dist_le_mul, mul_comm, nndist_comm, testAgains, testAgainstNN, testAgainstNN_lipschitz_estimate
-/
theorem testAgainstNN_lipschitz (μ : FiniteMeasure Ω) :
    LipschitzWith μ.mass fun f : Ω ->ᵇ Real>=0 => μ.testAgainstNN f := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro f₁ f₂
  suffices abs (μ.testAgainstNN f₁ - μ.testAgainstNN f₂ : Real) <= μ.mass * dist f₁ f₂ by
    rwa [NNReal.dist_eq]
  apply abs_le.mpr
  constructor
  · have key := μ.testAgainstNN_lipschitz_estimate f₂ f₁
    rw [mul_comm] at key
    suffices ↑(μ.testAgainstNN f₂) <= ↑(μ.testAgainstNN f₁) + ↑μ.mass * dist f₁ f₂ by linarith
    simpa [nndist_comm] using NNReal.coe_mono key
  · have key := μ.testAgainstNN_lipschitz_estimate f₁ f₂
    rw [mul_comm] at key
    suffices ↑(μ.testAgainstNN f₁) <= ↑(μ.testAgainstNN f₂) + ↑μ.mass * dist f₁ f₂ by linarith
    simpa using NNReal.coe_mono key

/--
Definition of `toWeakDualBCNN` / `toWeakDualBCNN` 的定义

English:
definition toWeakDualBCNN
  signature: (μ : FiniteMeasure Ω)
  body: μ.testAgainstNN f
  map_add' := testAgainstNN_add μ
  map_smul' := testAgainstNN_smul μ
  cont := μ.testAgainstNN_lipschitz.continuous

@[simp]

中文:
定义 toWeakDualBCNN
  签名: (μ : 有限测度 Ω)
  定义体: μ.testAgainstNN f
  map_add' := testAgainstNN_add μ
  map_smul' := testAgainstNN_smul μ
  cont := μ.testAgainstNN_lipschitz.continuous

@[simp]

Depends on / 依赖: testAgainstNN
-/
def toWeakDualBCNN (μ : FiniteMeasure Ω) : WeakDual Real>=0 (Ω ->ᵇ Real>=0) where
  toFun f := μ.testAgainstNN f
  map_add' := testAgainstNN_add μ
  map_smul' := testAgainstNN_smul μ
  cont := μ.testAgainstNN_lipschitz.continuous

@[simp]
/--
theorem `coe_toWeakDualBCNN` / 定理 `coe_toWeakDualBCNN`

English:
theorem coe_toWeakDualBCNN
  given: (μ : FiniteMeasure Ω)
  statement: ⇑μ.toWeakDualBCNN = μ.testAgainstNN
  proof: rfl

@[simp]

中文:
定理 coe_toWeakDualBCNN
  条件: (μ : 有限测度 Ω)
  结论: ⇑μ.toWeakDualBCNN = μ.testAgainstNN
  证明: rfl

@[simp]
-/
theorem coe_toWeakDualBCNN (μ : FiniteMeasure Ω) : ⇑μ.toWeakDualBCNN = μ.testAgainstNN :=
  rfl

@[simp]
/--
theorem `toWeakDualBCNN_apply` / 定理 `toWeakDualBCNN_apply`

English:
theorem toWeakDualBCNN_apply
  given: (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0)
  proof: rfl

中文:
定理 toWeakDualBCNN_apply
  条件: (μ : 有限测度 Ω) (f : Ω ->ᵇ 实数>=0)
  证明: rfl
-/
theorem toWeakDualBCNN_apply (μ : FiniteMeasure Ω) (f : Ω ->ᵇ Real>=0) :
    μ.toWeakDualBCNN f = (∫⁻ x, f x ∂(μ : Measure Ω)).toNNReal := rfl

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (FiniteMeasure Ω)
  body: TopologicalSpace.induced toWeakDualBCNN inferInstance

中文:
实例 instTopologicalSpace
  签名: : 拓扑空间 (有限测度 Ω)
  定义体: TopologicalSpace.induced toWeakDualBCNN inferInstance

Depends on / 依赖: TopologicalSpace, TopologicalSpace.induced, induced, toWeakDualBCNN
-/
instance instTopologicalSpace : TopologicalSpace (FiniteMeasure Ω) :=
  TopologicalSpace.induced toWeakDualBCNN inferInstance

/--
theorem `toWeakDualBCNN_continuous` / 定理 `toWeakDualBCNN_continuous`

English:
theorem toWeakDualBCNN_continuous
  statement: Continuous (@toWeakDualBCNN Ω _ _ _)
  proof: continuous_induced_dom

中文:
定理 toWeakDualBCNN_continuous
  结论: 连续 (@toWeakDualBCNN Ω _ _ _)
  证明: continuous_induced_dom

Depends on / 依赖: continuous_induced_dom
-/
theorem toWeakDualBCNN_continuous : Continuous (@toWeakDualBCNN Ω _ _ _) :=
  continuous_induced_dom

/--
theorem `continuous_testAgainstNN_eval` / 定理 `continuous_testAgainstNN_eval`

English:
theorem continuous_testAgainstNN_eval
  given: (f : Ω ->ᵇ Real>=0)
  proof: by
  change Continuous ((fun φ : WeakDual Real>=0 (Ω ->ᵇ Real>=0) => φ f) ∘ toWeakDualBCNN)
  refine Continuous.comp ?_ (toWeakDualBCNN_continuous (Ω := Ω))
  exact WeakBilin.eval_continuous _ _

中文:
定理 continuous_testAgainstNN_eval
  条件: (f : Ω ->ᵇ 实数>=0)
  证明: by
  change Continuous ((fun φ : WeakDual Real>=0 (Ω ->ᵇ Real>=0) => φ f) ∘ toWeakDualBCNN)
  refine Continuous.comp ?_ (toWeakDualBCNN_continuous (Ω := Ω))
  exact WeakBilin.eval_continuous _ _

Depends on / 依赖: Continuous, Continuous.comp, WeakBilin, WeakBilin.eval_continuous, WeakDual, eval_continuous, toWeakDualBCNN, toWeakDualBCNN_continuous
-/
theorem continuous_testAgainstNN_eval (f : Ω ->ᵇ Real>=0) :
    Continuous fun μ : FiniteMeasure Ω => μ.testAgainstNN f := by
  change Continuous ((fun φ : WeakDual Real>=0 (Ω ->ᵇ Real>=0) => φ f) ∘ toWeakDualBCNN)
  refine Continuous.comp ?_ (toWeakDualBCNN_continuous (Ω := Ω))
  exact WeakBilin.eval_continuous _ _

/--
theorem `continuous_mass` / 定理 `continuous_mass`

English:
theorem continuous_mass
  statement: Continuous fun μ : FiniteMeasure Ω => μ.mass
  proof: by
  simp_rw [← testAgainstNN_one]; exact continuous_testAgainstNN_eval 1

中文:
定理 continuous_mass
  结论: 连续 fun μ : 有限测度 Ω => μ.mass
  证明: by
  simp_rw [← testAgainstNN_one]; exact continuous_testAgainstNN_eval 1
-/
@[fun_prop] theorem continuous_mass : Continuous fun μ : FiniteMeasure Ω => μ.mass := by
  simp_rw [← testAgainstNN_one]; exact continuous_testAgainstNN_eval 1

/--
theorem `_root_.Filter.Tendsto.mass` / 定理 `_root_.Filter.Tendsto.mass`

English:
theorem _root_.Filter.Tendsto.mass
  statement: {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  proof: (continuous_mass.tendsto μ).comp h

中文:
定理 _root_.滤子.收敛.mass
  结论: {γ : 类型} {F : 滤子 γ} {μs : γ -> 有限测度 Ω}
  证明: (continuous_mass.tendsto μ).comp h

Depends on / 依赖: continuous_mass, continuous_mass.tendsto, tendsto
-/
theorem _root_.Filter.Tendsto.mass {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} (h : Tendsto μs F (𝓝 μ)) : Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass) :=
  (continuous_mass.tendsto μ).comp h

/--
theorem `tendsto_iff_weakDual_tendsto` / 定理 `tendsto_iff_weakDual_tendsto`

English:
theorem tendsto_iff_weakDual_tendsto
  statement: {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  proof: IsInducing.tendsto_nhds_iff ⟨rfl⟩

中文:
定理 tendsto_iff_weakDual_tendsto
  结论: {γ : 类型} {F : 滤子 γ} {μs : γ -> 有限测度 Ω}
  证明: IsInducing.tendsto_nhds_iff ⟨rfl⟩

Depends on / 依赖: IsInducing, IsInducing.tendsto_nhds_iff, tendsto_nhds_iff
-/
theorem tendsto_iff_weakDual_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔ Tendsto (fun i => (μs i).toWeakDualBCNN) F (𝓝 μ.toWeakDualBCNN) :=
  IsInducing.tendsto_nhds_iff ⟨rfl⟩

/--
theorem `tendsto_iff_forall_toWeakDualBCNN_tendsto` / 定理 `tendsto_iff_forall_toWeakDualBCNN_tendsto`

English:
theorem tendsto_iff_forall_toWeakDualBCNN_tendsto
  statement: {γ : Type*} {F : Filter γ}
  proof: by
  rw [tendsto_iff_weakDual_tendsto]; rw [tendsto_iff_forall_eval_tendsto_topDualPairing]; rfl

中文:
定理 tendsto_iff_对任意_toWeakDualBCNN_tendsto
  结论: {γ : 类型} {F : 滤子 γ}
  证明: by
  rw [tendsto_iff_weakDual_tendsto]; rw [tendsto_iff_forall_eval_tendsto_topDualPairing]; rfl

Depends on / 依赖: tendsto_iff_forall_eval_tendsto_topDualPairing, tendsto_iff_weakDual_tendsto
-/
theorem tendsto_iff_forall_toWeakDualBCNN_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ -> FiniteMeasure Ω} {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      forall f : Ω ->ᵇ Real>=0, Tendsto (fun i => (μs i).toWeakDualBCNN f) F (𝓝 (μ.toWeakDualBCNN f)) := by
  rw [tendsto_iff_weakDual_tendsto]; rw [tendsto_iff_forall_eval_tendsto_topDualPairing]; rfl

/--
theorem `tendsto_iff_forall_testAgainstNN_tendsto` / 定理 `tendsto_iff_forall_testAgainstNN_tendsto`

English:
theorem tendsto_iff_forall_testAgainstNN_tendsto
  statement: {γ : Type*} {F : Filter γ}
  proof: by
  rw [FiniteMeasure.tendsto_iff_forall_toWeakDualBCNN_tendsto]; rfl

中文:
定理 tendsto_iff_对任意_testAgainstNN_tendsto
  结论: {γ : 类型} {F : 滤子 γ}
  证明: by
  rw [FiniteMeasure.tendsto_iff_forall_toWeakDualBCNN_tendsto]; rfl

Depends on / 依赖: FiniteMeasure, FiniteMeasure.tendsto_iff_forall_toWeakDualBCNN_tendsto, tendsto_iff_forall_toWeakDualBCNN_tendsto
-/
theorem tendsto_iff_forall_testAgainstNN_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ -> FiniteMeasure Ω} {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      forall f : Ω ->ᵇ Real>=0, Tendsto (fun i => (μs i).testAgainstNN f) F (𝓝 (μ.testAgainstNN f)) := by
  rw [FiniteMeasure.tendsto_iff_forall_toWeakDualBCNN_tendsto]; rfl

/--
theorem `tendsto_zero_testAgainstNN_of_tendsto_zero_mass` / 定理 `tendsto_zero_testAgainstNN_of_tendsto_zero_mass`

English:
theorem tendsto_zero_testAgainstNN_of_tendsto_zero_mass
  statement: {γ : Type*} {F : Filter γ}
  proof: by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have obs := fun i => (μs i).testAgainstNN_lipschitz_estimate f 0
  simp_rw [testAgainstNN_zero, zero_add] at obs
  simp_rw [show forall i, dist ((μs i).testAgainstNN f) 0 = (μs i).testAgainstNN f by
      simp only [dist_nndist, NNReal.nndist_zero_eq_val', imp_true_iff]]
  apply squeeze_zero (fun i => NNReal.coe_nonneg _) obs
  have lim_pair : Tendsto (fun i => (⟨nndist f 0, (μs i).mass⟩ : Real × Real)) F (𝓝 ⟨nndist f 0, 0⟩) :=
    (Prod.tendsto_iff _ _).mpr ⟨tendsto_const_nhds, (NNReal.continuous_coe.tendsto 0).comp mass_lim⟩
  simpa using! tendsto_mul.comp lim_pair

中文:
定理 tendsto_zero_testAgainstNN_of_tendsto_zero_mass
  结论: {γ : 类型} {F : 滤子 γ}
  证明: by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have obs := fun i => (μs i).testAgainstNN_lipschitz_estimate f 0
  simp_rw [testAgainstNN_zero, zero_add] at obs
  simp_rw [show forall i, dist ((μs i).testAgainstNN f) 0 = (μs i).testAgainstNN f by
      simp only [dist_nndist, NNReal.nndist_zero_eq_val', imp_true_iff]]
  apply squeeze_zero (fun i => NNReal.coe_nonneg _) obs
  have lim_pair : Tendsto (fun i => (⟨nndist f 0, (μs i).mass⟩ : Real × Real)) F (𝓝 ⟨nndist f 0, 0⟩) :=
    (Prod.tendsto_iff _ _).mpr ⟨tendsto_const_nhds, (NNReal.continuous_coe.tendsto 0).comp mass_lim⟩
  simpa using! tendsto_mul.comp lim_pair

Depends on / 依赖: NNReal, NNReal.coe_nonneg, NNReal.nndist_zero_eq_val, Prod.tendsto_iff, Tendsto, coe_nonneg, dist_nndist, imp_true_iff, lim_pair, nndist, nndist_zero_eq_val, simp_rw, squeeze_zero, tendsto_con, tendsto_iff, tendsto_iff_dist_tendsto_zero, tendsto_iff_dist_tendsto_zero.mpr, testAgainstNN, testAgainstNN_lipschitz_estimate, testAgainstNN_zero
-/
theorem tendsto_zero_testAgainstNN_of_tendsto_zero_mass {γ : Type*} {F : Filter γ}
    {μs : γ -> FiniteMeasure Ω} (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 0)) (f : Ω ->ᵇ Real>=0) :
    Tendsto (fun i => (μs i).testAgainstNN f) F (𝓝 0) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have obs := fun i => (μs i).testAgainstNN_lipschitz_estimate f 0
  simp_rw [testAgainstNN_zero, zero_add] at obs
  simp_rw [show forall i, dist ((μs i).testAgainstNN f) 0 = (μs i).testAgainstNN f by
      simp only [dist_nndist, NNReal.nndist_zero_eq_val', imp_true_iff]]
  apply squeeze_zero (fun i => NNReal.coe_nonneg _) obs
  have lim_pair : Tendsto (fun i => (⟨nndist f 0, (μs i).mass⟩ : Real × Real)) F (𝓝 ⟨nndist f 0, 0⟩) :=
    (Prod.tendsto_iff _ _).mpr ⟨tendsto_const_nhds, (NNReal.continuous_coe.tendsto 0).comp mass_lim⟩
  simpa using! tendsto_mul.comp lim_pair

/--
theorem `tendsto_zero_of_tendsto_zero_mass` / 定理 `tendsto_zero_of_tendsto_zero_mass`

English:
theorem tendsto_zero_of_tendsto_zero_mass
  statement: {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  proof: by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  intro f
  convert! tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  rw [zero_testAgainstNN_apply]

中文:
定理 tendsto_zero_of_tendsto_zero_mass
  结论: {γ : 类型} {F : 滤子 γ} {μs : γ -> 有限测度 Ω}
  证明: by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  intro f
  convert! tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  rw [zero_testAgainstNN_apply]

Depends on / 依赖: convert, mass_lim, tendsto_iff_forall_testAgainstNN_tendsto, tendsto_zero_testAgainstNN_of_tendsto_zero_mass, zero_testAgainstNN_apply
-/
theorem tendsto_zero_of_tendsto_zero_mass {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
    (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 0)) : Tendsto μs F (𝓝 0) := by
  rw [tendsto_iff_forall_testAgainstNN_tendsto]
  intro f
  convert! tendsto_zero_testAgainstNN_of_tendsto_zero_mass mass_lim f
  rw [zero_testAgainstNN_apply]

/--
theorem `tendsto_iff_forall_lintegral_tendsto` / 定理 `tendsto_iff_forall_lintegral_tendsto`

English:
theorem tendsto_iff_forall_lintegral_tendsto
  statement: {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  proof: by
  rw [tendsto_iff_forall_toWeakDualBCNN_tendsto]
  simp_rw [toWeakDualBCNN_apply _ _, ← testAgainstNN_coe_eq, ENNReal.tendsto_coe,
    ENNReal.toNNReal_coe]

中文:
定理 tendsto_iff_对任意_lintegral_tendsto
  结论: {γ : 类型} {F : 滤子 γ} {μs : γ -> 有限测度 Ω}
  证明: by
  rw [tendsto_iff_forall_toWeakDualBCNN_tendsto]
  simp_rw [toWeakDualBCNN_apply _ _, ← testAgainstNN_coe_eq, ENNReal.tendsto_coe,
    ENNReal.toNNReal_coe]

Depends on / 依赖: ENNReal, ENNReal.tendsto_coe, ENNReal.toNNReal_coe, simp_rw, tendsto_coe, tendsto_iff_forall_toWeakDualBCNN_tendsto, testAgainstNN_coe_eq, toNNReal_coe, toWeakDualBCNN_apply
-/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      forall f : Ω ->ᵇ Real>=0,
        Tendsto (fun i => ∫⁻ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ x, f x ∂(μ : Measure Ω))) := by
  rw [tendsto_iff_forall_toWeakDualBCNN_tendsto]
  simp_rw [toWeakDualBCNN_apply _ _, ← testAgainstNN_coe_eq, ENNReal.tendsto_coe,
    ENNReal.toNNReal_coe]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: R1Space (FiniteMeasure Ω)
  body: IsInducing.r1Space (f := toWeakDualBCNN) ⟨rfl⟩

中文:
实例 :
  签名: R1空间 (有限测度 Ω)
  定义体: IsInducing.r1Space (f := toWeakDualBCNN) ⟨rfl⟩

Depends on / 依赖: IsInducing, IsInducing.r1Space, r1Space, toWeakDualBCNN
-/
instance : R1Space (FiniteMeasure Ω) := IsInducing.r1Space (f := toWeakDualBCNN) ⟨rfl⟩

end weak_convergence -- section

section Hausdorff

variable [HasOuterApproxClosed Ω] [BorelSpace Ω]

open Function

/--
lemma `injective_toWeakDualBCNN` / 引理 `injective_toWeakDualBCNN`

English:
lemma injective_toWeakDualBCNN
  proof: by
  intro μ ν hμν
  apply ext_of_forall_lintegral_eq
  intro f
  have key := congr_fun (congrArg DFunLike.coe hμν) f
  apply (ENNReal.toNNReal_eq_toNNReal_iff' ?_ ?_).mp key
  · exact (lintegral_lt_top_of_nnreal μ f).ne
  · exact (lintegral_lt_top_of_nnreal ν f).ne

中文:
引理 injective_toWeakDualBCNN
  证明: by
  intro μ ν hμν
  apply ext_of_forall_lintegral_eq
  intro f
  have key := congr_fun (congrArg DFunLike.coe hμν) f
  apply (ENNReal.toNNReal_eq_toNNReal_iff' ?_ ?_).mp key
  · exact (lintegral_lt_top_of_nnreal μ f).ne
  · exact (lintegral_lt_top_of_nnreal ν f).ne

Depends on / 依赖: DFunLike, DFunLike.coe, ENNReal, ENNReal.toNNReal_eq_toNNReal_iff, congr_fun, ext_of_forall_lintegral_eq, lintegral_lt_top_of_nnreal, toNNReal_eq_toNNReal_iff
-/
lemma injective_toWeakDualBCNN :
    Injective (toWeakDualBCNN : FiniteMeasure Ω -> WeakDual Real>=0 (Ω ->ᵇ Real>=0)) := by
  intro μ ν hμν
  apply ext_of_forall_lintegral_eq
  intro f
  have key := congr_fun (congrArg DFunLike.coe hμν) f
  apply (ENNReal.toNNReal_eq_toNNReal_iff' ?_ ?_).mp key
  · exact (lintegral_lt_top_of_nnreal μ f).ne
  · exact (lintegral_lt_top_of_nnreal ν f).ne

variable (Ω)

/--
lemma `isEmbedding_toWeakDualBCNN` / 引理 `isEmbedding_toWeakDualBCNN`

English:
lemma isEmbedding_toWeakDualBCNN
  proof: rfl
  injective := injective_toWeakDualBCNN

中文:
引理 isEmbedding_toWeakDualBCNN
  证明: rfl
  injective := injective_toWeakDualBCNN
-/
lemma isEmbedding_toWeakDualBCNN :
    IsEmbedding (toWeakDualBCNN : FiniteMeasure Ω -> WeakDual Real>=0 (Ω ->ᵇ Real>=0)) where
  eq_induced := rfl
  injective := injective_toWeakDualBCNN

/--
Instance `t2Space` / 实例 `t2Space`

English:
instance t2Space
  signature: : T2Space (FiniteMeasure Ω)
  body: (isEmbedding_toWeakDualBCNN Ω).t2Space

中文:
实例 t2Space
  签名: : T2空间 (有限测度 Ω)
  定义体: (isEmbedding_toWeakDualBCNN Ω).t2Space

Depends on / 依赖: isEmbedding_toWeakDualBCNN, t2Space
-/
instance t2Space : T2Space (FiniteMeasure Ω) := (isEmbedding_toWeakDualBCNN Ω).t2Space

end Hausdorff -- section

end FiniteMeasure

-- section
section FiniteMeasureBoundedConvergence

/-! ### Bounded convergence results for finite measures

This section is about bounded convergence theorems for finite measures.
-/


variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/--
theorem `tendsto_lintegral_nn_of_le_const` / 定理 `tendsto_lintegral_nn_of_le_const`

English:
theorem tendsto_lintegral_nn_of_le_const
  statement: (μ : FiniteMeasure Ω) {fs : Nat -> Ω ->ᵇ Real>=0} {c : Real>=0}
  proof: tendsto_lintegral_nn_filter_of_le_const μ
    (.of_forall fun n => .of_forall (fs_le_const n))
    (.of_forall fs_lim)

中文:
定理 tendsto_lintegral_nn_of_le_const
  结论: (μ : 有限测度 Ω) {fs : 自然数 -> Ω ->ᵇ 实数>=0} {c : 实数>=0}
  证明: tendsto_lintegral_nn_filter_of_le_const μ
    (.of_forall fun n => .of_forall (fs_le_const n))
    (.of_forall fs_lim)

Depends on / 依赖: fs_le_const, fs_lim, of_forall, tendsto_lintegral_nn_filter_of_le_const
-/
theorem tendsto_lintegral_nn_of_le_const (μ : FiniteMeasure Ω) {fs : Nat -> Ω ->ᵇ Real>=0} {c : Real>=0}
    (fs_le_const : forall n ω, fs n ω <= c) {f : Ω -> Real>=0}
    (fs_lim : forall ω, Tendsto (fun n => fs n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n => ∫⁻ ω, fs n ω ∂(μ : Measure Ω)) atTop (𝓝 (∫⁻ ω, f ω ∂(μ : Measure Ω))) :=
  tendsto_lintegral_nn_filter_of_le_const μ
    (.of_forall fun n => .of_forall (fs_le_const n))
    (.of_forall fs_lim)

/--
theorem `tendsto_testAgainstNN_filter_of_le_const` / 定理 `tendsto_testAgainstNN_filter_of_le_const`

English:
theorem tendsto_testAgainstNN_filter_of_le_const
  statement: {ι : Type*} {L : Filter ι}
  proof: by
  apply (ENNReal.tendsto_toNNReal (f.lintegral_lt_top_of_nnreal (μ : Measure Ω)).ne).comp
  exact tendsto_lintegral_nn_filter_of_le_const (Ω := Ω) μ fs_le_const fs_lim

中文:
定理 tendsto_testAgainstNN_filter_of_le_const
  结论: {ι : 类型} {L : 滤子 ι}
  证明: by
  apply (ENNReal.tendsto_toNNReal (f.lintegral_lt_top_of_nnreal (μ : Measure Ω)).ne).comp
  exact tendsto_lintegral_nn_filter_of_le_const (Ω := Ω) μ fs_le_const fs_lim

Depends on / 依赖: ENNReal, ENNReal.tendsto_toNNReal, Measure, f.lintegral_lt_top_of_nnreal, fs_le_const, fs_lim, lintegral_lt_top_of_nnreal, tendsto_lintegral_nn_filter_of_le_const, tendsto_toNNReal
-/
theorem tendsto_testAgainstNN_filter_of_le_const {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {μ : FiniteMeasure Ω} {fs : ι -> Ω ->ᵇ Real>=0} {c : Real>=0}
    (fs_le_const : forallᶠ i in L, forallᵐ ω : Ω ∂(μ : Measure Ω), fs i ω <= c) {f : Ω ->ᵇ Real>=0}
    (fs_lim : forallᵐ ω : Ω ∂(μ : Measure Ω), Tendsto (fun i => fs i ω) L (𝓝 (f ω))) :
    Tendsto (fun i => μ.testAgainstNN (fs i)) L (𝓝 (μ.testAgainstNN f)) := by
  apply (ENNReal.tendsto_toNNReal (f.lintegral_lt_top_of_nnreal (μ : Measure Ω)).ne).comp
  exact tendsto_lintegral_nn_filter_of_le_const (Ω := Ω) μ fs_le_const fs_lim

/--
theorem `tendsto_testAgainstNN_of_le_const` / 定理 `tendsto_testAgainstNN_of_le_const`

English:
theorem tendsto_testAgainstNN_of_le_const
  statement: {μ : FiniteMeasure Ω} {fs : Nat -> Ω ->ᵇ Real>=0} {c : Real>=0}
  proof: tendsto_testAgainstNN_filter_of_le_const
    (.of_forall fun n => .of_forall (fs_le_const n))
    (.of_forall fs_lim)

中文:
定理 tendsto_testAgainstNN_of_le_const
  结论: {μ : 有限测度 Ω} {fs : 自然数 -> Ω ->ᵇ 实数>=0} {c : 实数>=0}
  证明: tendsto_testAgainstNN_filter_of_le_const
    (.of_forall fun n => .of_forall (fs_le_const n))
    (.of_forall fs_lim)

Depends on / 依赖: fs_le_const, fs_lim, of_forall, tendsto_testAgainstNN_filter_of_le_const
-/
theorem tendsto_testAgainstNN_of_le_const {μ : FiniteMeasure Ω} {fs : Nat -> Ω ->ᵇ Real>=0} {c : Real>=0}
    (fs_le_const : forall n ω, fs n ω <= c) {f : Ω ->ᵇ Real>=0}
    (fs_lim : forall ω, Tendsto (fun n => fs n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n => μ.testAgainstNN (fs n)) atTop (𝓝 (μ.testAgainstNN f)) :=
  tendsto_testAgainstNN_filter_of_le_const
    (.of_forall fun n => .of_forall (fs_le_const n))
    (.of_forall fs_lim)

end FiniteMeasureBoundedConvergence

-- section
section FiniteMeasureConvergenceByBoundedContinuousFunctions

/-! ### Weak convergence of finite measures with bounded continuous real-valued functions

In this section we characterize the weak convergence of finite measures by the usual (defining)
condition that the integrals of all bounded continuous real-valued functions converge.
-/


variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/--
theorem `tendsto_of_forall_integral_tendsto` / 定理 `tendsto_of_forall_integral_tendsto`

English:
theorem tendsto_of_forall_integral_tendsto
  statement: {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  proof: by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro f
  apply (ENNReal.tendsto_toReal_iff (fi := F)
      (fun i => (f.lintegral_lt_top_of_nnreal (μs i)).ne) (f.lintegral_lt_top_of_nnreal μ).ne).mp
  have lip : LipschitzWith 1 ((↑) : Real>=0 -> Real) := NNReal.isometry_coe.lipschitz
  set f₀ := BoundedContinuousFunction.comp _ lip f with _def_f₀
  have f₀_eq : ⇑f₀ = ((↑) : Real>=0 -> Real) ∘ ⇑f := rfl
  have f₀_nn : 0 <= ⇑f₀ := fun _ => by
    simp only [f₀_eq, Pi.zero_apply, Function.comp_apply, NNReal.zero_le_coe]
  have f₀_ae_nn : 0 <=ᵐ[(μ : Measure Ω)] ⇑f₀ := .of_forall f₀_nn
  have f₀_ae_nns : forall i, 0 <=ᵐ[(μs i : Measure Ω)] ⇑f₀ := fun i => .of_forall f₀_nn
  have aux :=
    integral_eq_lintegral_of_nonneg_ae f₀_ae_nn f₀.continuous.measurable.aestronglyMeasurable
  have auxs := fun i =>
    integral_eq_lintegral_of_nonneg_ae (f₀_ae_nns i) f₀.continuous.measurable.aestronglyMeasurable
  simp_rw [f₀_eq, Function.comp_apply, ENNReal.ofReal_coe_nnreal] at aux auxs
  simpa only [← aux, ← auxs] using! h f₀

中文:
定理 tendsto_of_对任意_integral_tendsto
  结论: {γ : 类型} {F : 滤子 γ} {μs : γ -> 有限测度 Ω}
  证明: by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro f
  apply (ENNReal.tendsto_toReal_iff (fi := F)
      (fun i => (f.lintegral_lt_top_of_nnreal (μs i)).ne) (f.lintegral_lt_top_of_nnreal μ).ne).mp
  have lip : LipschitzWith 1 ((↑) : Real>=0 -> Real) := NNReal.isometry_coe.lipschitz
  set f₀ := BoundedContinuousFunction.comp _ lip f with _def_f₀
  have f₀_eq : ⇑f₀ = ((↑) : Real>=0 -> Real) ∘ ⇑f := rfl
  have f₀_nn : 0 <= ⇑f₀ := fun _ => by
    simp only [f₀_eq, Pi.zero_apply, Function.comp_apply, NNReal.zero_le_coe]
  have f₀_ae_nn : 0 <=ᵐ[(μ : Measure Ω)] ⇑f₀ := .of_forall f₀_nn
  have f₀_ae_nns : forall i, 0 <=ᵐ[(μs i : Measure Ω)] ⇑f₀ := fun i => .of_forall f₀_nn
  have aux :=
    integral_eq_lintegral_of_nonneg_ae f₀_ae_nn f₀.continuous.measurable.aestronglyMeasurable
  have auxs := fun i =>
    integral_eq_lintegral_of_nonneg_ae (f₀_ae_nns i) f₀.continuous.measurable.aestronglyMeasurable
  simp_rw [f₀_eq, Function.comp_apply, ENNReal.ofReal_coe_nnreal] at aux auxs
  simpa only [← aux, ← auxs] using! h f₀

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.comp, ENNReal, ENNReal.tendsto_toReal_iff, Function, Function.comp_apply, LipschitzWith, NNReal, NNReal.isometry_coe.lipschitz, NNReal.zero_le, Pi.zero_apply, comp_apply, f.lintegral_lt_top_of_nnreal, isometry_coe, lintegral_lt_top_of_nnreal, lipschitz, tendsto_iff_forall_lintegral_tendsto, tendsto_iff_forall_lintegral_tendsto.mpr, tendsto_toReal_iff, zero_apply
-/
theorem tendsto_of_forall_integral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
    {μ : FiniteMeasure Ω}
    (h : forall f : Ω ->ᵇ Real,
          Tendsto (fun i => ∫ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫ x, f x ∂(μ : Measure Ω)))) :
    Tendsto μs F (𝓝 μ) := by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro f
  apply (ENNReal.tendsto_toReal_iff (fi := F)
      (fun i => (f.lintegral_lt_top_of_nnreal (μs i)).ne) (f.lintegral_lt_top_of_nnreal μ).ne).mp
  have lip : LipschitzWith 1 ((↑) : Real>=0 -> Real) := NNReal.isometry_coe.lipschitz
  set f₀ := BoundedContinuousFunction.comp _ lip f with _def_f₀
  have f₀_eq : ⇑f₀ = ((↑) : Real>=0 -> Real) ∘ ⇑f := rfl
  have f₀_nn : 0 <= ⇑f₀ := fun _ => by
    simp only [f₀_eq, Pi.zero_apply, Function.comp_apply, NNReal.zero_le_coe]
  have f₀_ae_nn : 0 <=ᵐ[(μ : Measure Ω)] ⇑f₀ := .of_forall f₀_nn
  have f₀_ae_nns : forall i, 0 <=ᵐ[(μs i : Measure Ω)] ⇑f₀ := fun i => .of_forall f₀_nn
  have aux :=
    integral_eq_lintegral_of_nonneg_ae f₀_ae_nn f₀.continuous.measurable.aestronglyMeasurable
  have auxs := fun i =>
    integral_eq_lintegral_of_nonneg_ae (f₀_ae_nns i) f₀.continuous.measurable.aestronglyMeasurable
  simp_rw [f₀_eq, Function.comp_apply, ENNReal.ofReal_coe_nnreal] at aux auxs
  simpa only [← aux, ← auxs] using! h f₀

/--
theorem `tendsto_iff_forall_integral_tendsto` / 定理 `tendsto_iff_forall_integral_tendsto`

English:
theorem tendsto_iff_forall_integral_tendsto
  statement: {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
  proof: by
  refine ⟨?_, tendsto_of_forall_integral_tendsto⟩
  rw [tendsto_iff_forall_lintegral_tendsto]
  intro h f
  simp_rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub]
  set f_pos := f.nnrealPart with _def_f_pos
  set f_neg := (-f).nnrealPart with _def_f_neg
  have tends_pos := (ENNReal.tendsto_toReal (f_pos.lintegral_lt_top_of_nnreal μ).ne).comp (h f_pos)
  have tends_neg := (ENNReal.tendsto_toReal (f_neg.lintegral_lt_top_of_nnreal μ).ne).comp (h f_neg)
  have aux :
    forall g : Ω ->ᵇ Real>=0,
      (ENNReal.toReal ∘ fun i : γ => ∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)) =
        fun i : γ => (∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)).toReal :=
    fun _ => rfl
  simp_rw [aux, BoundedContinuousFunction.toReal_lintegral_coe_eq_integral] at tends_pos tends_neg
  exact Tendsto.sub tends_pos tends_neg

中文:
定理 tendsto_iff_对任意_integral_tendsto
  结论: {γ : 类型} {F : 滤子 γ} {μs : γ -> 有限测度 Ω}
  证明: by
  refine ⟨?_, tendsto_of_forall_integral_tendsto⟩
  rw [tendsto_iff_forall_lintegral_tendsto]
  intro h f
  simp_rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub]
  set f_pos := f.nnrealPart with _def_f_pos
  set f_neg := (-f).nnrealPart with _def_f_neg
  have tends_pos := (ENNReal.tendsto_toReal (f_pos.lintegral_lt_top_of_nnreal μ).ne).comp (h f_pos)
  have tends_neg := (ENNReal.tendsto_toReal (f_neg.lintegral_lt_top_of_nnreal μ).ne).comp (h f_neg)
  have aux :
    forall g : Ω ->ᵇ Real>=0,
      (ENNReal.toReal ∘ fun i : γ => ∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)) =
        fun i : γ => (∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)).toReal :=
    fun _ => rfl
  simp_rw [aux, BoundedContinuousFunction.toReal_lintegral_coe_eq_integral] at tends_pos tends_neg
  exact Tendsto.sub tends_pos tends_neg

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub, ENNReal, ENNReal.tendsto_toReal, _def_f_neg, _def_f_pos, f.nnrealPart, f_neg, f_neg.lintegral_lt_top_of_nnreal, f_pos, f_pos.lintegral_lt_top_of_nnreal, integral_eq_integral_nnrealPart_sub, lintegral_lt_top_of_nnreal, nnrealPart, simp_rw, tends_neg, tends_pos, tendsto_iff_forall_lintegral_tendsto, tendsto_of_forall_integral_tendsto, tendsto_toReal
-/
theorem tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      forall f : Ω ->ᵇ Real,
        Tendsto (fun i => ∫ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  refine ⟨?_, tendsto_of_forall_integral_tendsto⟩
  rw [tendsto_iff_forall_lintegral_tendsto]
  intro h f
  simp_rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub]
  set f_pos := f.nnrealPart with _def_f_pos
  set f_neg := (-f).nnrealPart with _def_f_neg
  have tends_pos := (ENNReal.tendsto_toReal (f_pos.lintegral_lt_top_of_nnreal μ).ne).comp (h f_pos)
  have tends_neg := (ENNReal.tendsto_toReal (f_neg.lintegral_lt_top_of_nnreal μ).ne).comp (h f_neg)
  have aux :
    forall g : Ω ->ᵇ Real>=0,
      (ENNReal.toReal ∘ fun i : γ => ∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)) =
        fun i : γ => (∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)).toReal :=
    fun _ => rfl
  simp_rw [aux, BoundedContinuousFunction.toReal_lintegral_coe_eq_integral] at tends_pos tends_neg
  exact Tendsto.sub tends_pos tends_neg

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tendsto_iff_forall_integral_rclike_tendsto` / 定理 `tendsto_iff_forall_integral_rclike_tendsto`

English:
theorem tendsto_iff_forall_integral_rclike_tendsto
  statement: {γ : Type*} (𝕜 : Type*) [RCLike 𝕜]
  proof: by
  rw [tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f => ?_, fun h f => ?_⟩
  · rw [← integral_re_add_im (integrable μ f)]
    simp_rw [← integral_re_add_im (integrable (μs _) f)]
    refine Tendsto.add ?_ ?_
    · exact (RCLike.continuous_ofReal.tendsto _).comp (h (f.comp RCLike.re RCLike.lipschitzWith_re))
    · exact (Tendsto.comp (RCLike.continuous_ofReal.tendsto _)
        (h (f.comp RCLike.im RCLike.lipschitzWith_im))).mul_const _
  · specialize h ((RCLike.ofRealAm (K := 𝕜)).compLeftContinuousBounded Real
      RCLike.lipschitzWith_ofReal f)
    simp only [AlgHom.compLeftContinuousBounded_apply_apply, RCLike.ofRealAm_coe,
      integral_ofReal] at h
    exact tendsto_ofReal_iff'.mp h

中文:
定理 tendsto_iff_对任意_integral_rclike_tendsto
  结论: {γ : 类型} (𝕜 : 类型) [RCLike 𝕜]
  证明: by
  rw [tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f => ?_, fun h f => ?_⟩
  · rw [← integral_re_add_im (integrable μ f)]
    simp_rw [← integral_re_add_im (integrable (μs _) f)]
    refine Tendsto.add ?_ ?_
    · exact (RCLike.continuous_ofReal.tendsto _).comp (h (f.comp RCLike.re RCLike.lipschitzWith_re))
    · exact (Tendsto.comp (RCLike.continuous_ofReal.tendsto _)
        (h (f.comp RCLike.im RCLike.lipschitzWith_im))).mul_const _
  · specialize h ((RCLike.ofRealAm (K := 𝕜)).compLeftContinuousBounded Real
      RCLike.lipschitzWith_ofReal f)
    simp only [AlgHom.compLeftContinuousBounded_apply_apply, RCLike.ofRealAm_coe,
      integral_ofReal] at h
    exact tendsto_ofReal_iff'.mp h

Depends on / 依赖: RCLike, RCLike.continuous_ofReal.tendsto, RCLike.im, RCLike.lipschitzWith_im, RCLike.lipschitzWith_re, RCLike.ofRealAm, RCLike.re, Tendsto, Tendsto.add, Tendsto.comp, compLeftContinuousBounded, continuous_ofReal, f.comp, integrable, integral_re_add_im, lipschitzWith_im, lipschitzWith_re, mul_const, ofRealAm, simp_rw
-/
theorem tendsto_iff_forall_integral_rclike_tendsto {γ : Type*} (𝕜 : Type*) [RCLike 𝕜]
    {F : Filter γ} {μs : γ -> FiniteMeasure Ω} {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      forall f : Ω ->ᵇ 𝕜,
        Tendsto (fun i => ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  rw [tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f => ?_, fun h f => ?_⟩
  · rw [← integral_re_add_im (integrable μ f)]
    simp_rw [← integral_re_add_im (integrable (μs _) f)]
    refine Tendsto.add ?_ ?_
    · exact (RCLike.continuous_ofReal.tendsto _).comp (h (f.comp RCLike.re RCLike.lipschitzWith_re))
    · exact (Tendsto.comp (RCLike.continuous_ofReal.tendsto _)
        (h (f.comp RCLike.im RCLike.lipschitzWith_im))).mul_const _
  · specialize h ((RCLike.ofRealAm (K := 𝕜)).compLeftContinuousBounded Real
      RCLike.lipschitzWith_ofReal f)
    simp only [AlgHom.compLeftContinuousBounded_apply_apply, RCLike.ofRealAm_coe,
      integral_ofReal] at h
    exact tendsto_ofReal_iff'.mp h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousAdd (FiniteMeasure Ω)
  body: by
  refine ⟨continuous_iff_continuousAt.2 (fun p => ?_)⟩
  apply tendsto_iff_forall_lintegral_tendsto.2 (fun g => ?_)
  have A : Tendsto (fun (i : FiniteMeasure Ω × FiniteMeasure Ω) => ∫⁻ x, g x ∂i.1) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.1)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_fst
  have B : Tendsto (fun (i : FiniteMeasure Ω × FiniteMeasure Ω) => ∫⁻ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert! A.add B with q <;> simp

中文:
实例 :
  签名: 连续加法 (有限测度 Ω)
  定义体: by
  refine ⟨continuous_iff_continuousAt.2 (fun p => ?_)⟩
  apply tendsto_iff_forall_lintegral_tendsto.2 (fun g => ?_)
  have A : Tendsto (fun (i : FiniteMeasure Ω × FiniteMeasure Ω) => ∫⁻ x, g x ∂i.1) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.1)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_fst
  have B : Tendsto (fun (i : FiniteMeasure Ω × FiniteMeasure Ω) => ∫⁻ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert! A.add B with q <;> simp

Depends on / 依赖: FiniteMeasure, Tendsto, continuous_iff_continuousAt, nhds_prod_eq, tendsto_fst, tendsto_id, tendsto_iff_forall_lintegral_tendsto
-/
instance : ContinuousAdd (FiniteMeasure Ω) := by
  refine ⟨continuous_iff_continuousAt.2 (fun p => ?_)⟩
  apply tendsto_iff_forall_lintegral_tendsto.2 (fun g => ?_)
  have A : Tendsto (fun (i : FiniteMeasure Ω × FiniteMeasure Ω) => ∫⁻ x, g x ∂i.1) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.1)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_fst
  have B : Tendsto (fun (i : FiniteMeasure Ω × FiniteMeasure Ω) => ∫⁻ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert! A.add B with q <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSMul Real>=0 (FiniteMeasure Ω)
  body: by
  refine ⟨continuous_iff_continuousAt.2 (fun p => ?_)⟩
  apply tendsto_iff_forall_integral_tendsto.2 (fun g => ?_)
  have A : Tendsto (fun (i : Real>=0 × FiniteMeasure Ω) => i.1) (𝓝 p) (𝓝 (p.1)) := by
    rw [nhds_prod_eq]
    exact tendsto_fst
  have B : Tendsto (fun (i : Real>=0 × FiniteMeasure Ω) => ∫ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_integral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert! A.smul B with q <;> simp

中文:
实例 :
  签名: 连续标量乘法 实数>=0 (有限测度 Ω)
  定义体: by
  refine ⟨continuous_iff_continuousAt.2 (fun p => ?_)⟩
  apply tendsto_iff_forall_integral_tendsto.2 (fun g => ?_)
  have A : Tendsto (fun (i : Real>=0 × FiniteMeasure Ω) => i.1) (𝓝 p) (𝓝 (p.1)) := by
    rw [nhds_prod_eq]
    exact tendsto_fst
  have B : Tendsto (fun (i : Real>=0 × FiniteMeasure Ω) => ∫ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_integral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert! A.smul B with q <;> simp

Depends on / 依赖: A.smul, FiniteMeasure, Tendsto, continuous_iff_continuousAt, convert, nhds_prod_eq, tendsto_fst, tendsto_id, tendsto_iff_forall_integral_tendsto, tendsto_snd
-/
instance : ContinuousSMul Real>=0 (FiniteMeasure Ω) := by
  refine ⟨continuous_iff_continuousAt.2 (fun p => ?_)⟩
  apply tendsto_iff_forall_integral_tendsto.2 (fun g => ?_)
  have A : Tendsto (fun (i : Real>=0 × FiniteMeasure Ω) => i.1) (𝓝 p) (𝓝 (p.1)) := by
    rw [nhds_prod_eq]
    exact tendsto_fst
  have B : Tendsto (fun (i : Real>=0 × FiniteMeasure Ω) => ∫ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_integral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert! A.smul B with q <;> simp

variable {X : Type*} [TopologicalSpace X] {μs : X -> FiniteMeasure Ω}

/--
lemma `continuous_iff_forall_continuous_lintegral` / 引理 `continuous_iff_forall_continuous_lintegral`

English:
lemma continuous_iff_forall_continuous_lintegral
  proof: by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_lintegral_tendsto,
    forall_comm (α := X)]

中文:
引理 continuous_iff_对任意_continuous_lintegral
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

@[fun_prop]

中文:
引理 continuous_iff_对任意_continuous_integral
  证明: by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_integral_tendsto,
    forall_comm (α := X)]

@[fun_prop]

Depends on / 依赖: ContinuousAt, continuous_iff_continuousAt, forall_comm, tendsto_iff_forall_integral_tendsto
-/
lemma continuous_iff_forall_continuous_integral :
    Continuous μs ↔ forall f : Ω ->ᵇ Real, Continuous fun x => ∫ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_integral_tendsto,
    forall_comm (α := X)]

@[fun_prop]
/--
lemma `continuous_lintegral_boundedContinuousFunction` / 引理 `continuous_lintegral_boundedContinuousFunction`

English:
lemma continuous_lintegral_boundedContinuousFunction
  statement: [MeasurableSpace X] [OpensMeasurableSpace X]
  proof: continuous_iff_forall_continuous_lintegral.1 continuous_id _

@[fun_prop]

中文:
引理 continuous_lintegral_boundedContinuousFunction
  结论: [可测空间 X] [OpensMeasurable空间 X]
  证明: continuous_iff_forall_continuous_lintegral.1 continuous_id _

@[fun_prop]

Depends on / 依赖: continuous_id, continuous_iff_forall_continuous_lintegral
-/
lemma continuous_lintegral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X ->ᵇ Real>=0) : Continuous fun μ : FiniteMeasure X => ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuous_lintegral.1 continuous_id _

@[fun_prop]
/--
lemma `continuous_integral_boundedContinuousFunction` / 引理 `continuous_integral_boundedContinuousFunction`

English:
lemma continuous_integral_boundedContinuousFunction
  statement: [MeasurableSpace X] [OpensMeasurableSpace X]
  proof: continuous_iff_forall_continuous_integral.1 continuous_id _

中文:
引理 continuous_integral_boundedContinuousFunction
  结论: [可测空间 X] [OpensMeasurable空间 X]
  证明: continuous_iff_forall_continuous_integral.1 continuous_id _

Depends on / 依赖: continuous_id, continuous_iff_forall_continuous_integral
-/
lemma continuous_integral_boundedContinuousFunction [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X ->ᵇ Real) : Continuous fun μ : FiniteMeasure X => ∫ x, f x ∂μ :=
  continuous_iff_forall_continuous_integral.1 continuous_id _

variable [CompactSpace Ω]

/--
lemma `continuous_iff_forall_continuousMap_continuous_lintegral` / 引理 `continuous_iff_forall_continuousMap_continuous_lintegral`

English:
lemma continuous_iff_forall_continuousMap_continuous_lintegral
  proof: continuous_iff_forall_continuous_lintegral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

中文:
引理 continuous_iff_对任意_continuousMap_continuous_lintegral
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
引理 continuous_iff_对任意_continuousMap_continuous_integral
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
  条件: [函数状 F X 实数>=0] [连续映射类 F X 实数>=0] (f : F)
  证明: continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩

Depends on / 依赖: continuous_id, continuous_iff_forall_continuousMap_continuous_lintegral, map_continuous
-/
lemma continuous_lintegral_continuousMap [FunLike F X Real>=0] [ContinuousMapClass F X Real>=0] (f : F) :
    Continuous fun μ : FiniteMeasure X => ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩

/--
lemma `continuous_integral_continuousMap` / 引理 `continuous_integral_continuousMap`

English:
lemma continuous_integral_continuousMap
  given: [FunLike F X Real] [ContinuousMapClass F X Real] (f : F)
  proof: continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

中文:
引理 continuous_integral_continuousMap
  条件: [函数状 F X 实数] [连续映射类 F X 实数] (f : F)
  证明: continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

Depends on / 依赖: continuous_id, continuous_iff_forall_continuousMap_continuous_integral, map_continuous
-/
lemma continuous_integral_continuousMap [FunLike F X Real] [ContinuousMapClass F X Real] (f : F) :
    Continuous fun μ : FiniteMeasure X => ∫ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

end FiniteMeasureConvergenceByBoundedContinuousFunctions -- section


section comap

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  body: ⟨Measure.comap f μ, by infer_instance⟩

中文:
定义 comap
  定义体: ⟨Measure.comap f μ, by infer_instance⟩

Depends on / 依赖: Measure, Measure.comap, infer_instance
-/
noncomputable def comap
    (f : Ω -> Ω') (μ : FiniteMeasure Ω') : FiniteMeasure Ω :=
  ⟨Measure.comap f μ, by infer_instance⟩

/--
lemma `toMeasure_comap` / 引理 `toMeasure_comap`

English:
lemma toMeasure_comap
  given: (f : Ω -> Ω') (μ : FiniteMeasure Ω')
  proof: rfl

中文:
引理 toMeasure_comap
  条件: (f : Ω -> Ω') (μ : 有限测度 Ω')
  证明: rfl
-/
@[simp] lemma toMeasure_comap (f : Ω -> Ω') (μ : FiniteMeasure Ω') :
    (μ.comap f).toMeasure = (μ : Measure Ω').comap f := rfl

/--
lemma `mass_comap_le` / 引理 `mass_comap_le`

English:
lemma mass_comap_le
  given: (f : Ω -> Ω') (μ : FiniteMeasure Ω')
  proof: by
  simp only [mass, comap, mk_apply, coeFn_def, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  apply (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans (measure_mono (subset_univ _))

中文:
引理 mass_comap_le
  条件: (f : Ω -> Ω') (μ : 有限测度 Ω')
  证明: by
  simp only [mass, comap, mk_apply, coeFn_def, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  apply (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans (measure_mono (subset_univ _))

Depends on / 依赖: ENNReal, ENNReal.toNNReal_le_toNNReal, Measure, Measure.comap_apply_le, coeFn_def, comap_apply_le, measure_mono, measure_ne_top, mk_apply, ne_eq, not_false_eq_true, nullMeasurableSet_univ, subset_univ, toNNReal_le_toNNReal
-/
lemma mass_comap_le (f : Ω -> Ω') (μ : FiniteMeasure Ω') :
    (μ.comap f).mass <= μ.mass := by
  simp only [mass, comap, mk_apply, coeFn_def, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  apply (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans (measure_mono (subset_univ _))

variable [TopologicalSpace Ω] [TopologicalSpace Ω'] [BorelSpace Ω] [BorelSpace Ω']

/--
lemma `_root_.Topology.IsClosedEmbedding.continuousOn_comap_finiteMeasure` / 引理 `_root_.Topology.IsClosedEmbedding.continuousOn_comap_finiteMeasure`

English:
lemma _root_.Topology.IsClosedEmbedding.continuousOn_comap_finiteMeasure
  statement: [NormalSpace Ω']
  proof: by
  intro μ hμ
  simp only [ContinuousWithinAt]
  rw [tendsto_iff_forall_integral_tendsto]
  intro g
  obtain ⟨g', -, hg'⟩ : exists g' : Ω' ->ᵇ Real, ‖g'‖ = ‖g‖ ∧ g' ∘ f = g :=
    exists_extension_norm_eq_of_isClosedEmbedding g hf
  have A x : g x = g' (f x) := by change (⇑g) x = (⇑g' ∘ f) x; simp only [hg']
  simp only [comap, toMeasure_mk, A, ← MeasurableEmbedding.integral_map hf.measurableEmbedding,
    MeasurableEmbedding.map_comap hf.measurableEmbedding]
  have B {ν : FiniteMeasure Ω'} (hν : ν (range f)ᶜ = 0) :
      ∫ y in range f, g' y ∂ν = ∫ y, g' y ∂ν := by
    congr
    simp only [null_iff_toMeasure_null] at hν
    exact Measure.restrict_eq_self_of_ae_mem hν
  rw [B hμ]
  have : Tendsto (fun (ν : FiniteMeasure Ω') => ∫ y, g' y ∂ν) (𝓝[{μ | μ (range f)ᶜ = 0}] μ)
      (𝓝 (∫ (y : Ω'), g' y ∂μ)) := by
    rw [nhdsWithin]
    have A : Tendsto (fun (ν : FiniteMeasure Ω') => ∫ y, g' y ∂ν) (𝓝 μ) (𝓝 (∫ (y : Ω'), g' y ∂μ)) :=
      tendsto_iff_forall_integral_tendsto.1 tendsto_id _
    exact Tendsto.mono_left A inf_le_left
  apply Tendsto.congr' _ this
  filter_upwards [self_mem_nhdsWithin] with ν hν using (B hν).symm

中文:
引理 _root_.拓扑.是闭嵌入.continuousOn_comap_finiteMeasure
  结论: [正规空间 Ω']
  证明: by
  intro μ hμ
  simp only [ContinuousWithinAt]
  rw [tendsto_iff_forall_integral_tendsto]
  intro g
  obtain ⟨g', -, hg'⟩ : exists g' : Ω' ->ᵇ Real, ‖g'‖ = ‖g‖ ∧ g' ∘ f = g :=
    exists_extension_norm_eq_of_isClosedEmbedding g hf
  have A x : g x = g' (f x) := by change (⇑g) x = (⇑g' ∘ f) x; simp only [hg']
  simp only [comap, toMeasure_mk, A, ← MeasurableEmbedding.integral_map hf.measurableEmbedding,
    MeasurableEmbedding.map_comap hf.measurableEmbedding]
  have B {ν : FiniteMeasure Ω'} (hν : ν (range f)ᶜ = 0) :
      ∫ y in range f, g' y ∂ν = ∫ y, g' y ∂ν := by
    congr
    simp only [null_iff_toMeasure_null] at hν
    exact Measure.restrict_eq_self_of_ae_mem hν
  rw [B hμ]
  have : Tendsto (fun (ν : FiniteMeasure Ω') => ∫ y, g' y ∂ν) (𝓝[{μ | μ (range f)ᶜ = 0}] μ)
      (𝓝 (∫ (y : Ω'), g' y ∂μ)) := by
    rw [nhdsWithin]
    have A : Tendsto (fun (ν : FiniteMeasure Ω') => ∫ y, g' y ∂ν) (𝓝 μ) (𝓝 (∫ (y : Ω'), g' y ∂μ)) :=
      tendsto_iff_forall_integral_tendsto.1 tendsto_id _
    exact Tendsto.mono_left A inf_le_left
  apply Tendsto.congr' _ this
  filter_upwards [self_mem_nhdsWithin] with ν hν using (B hν).symm

Depends on / 依赖: ContinuousWithinAt, FiniteMeasure, MeasurableEmbedding, MeasurableEmbedding.integral_map, MeasurableEmbedding.map_comap, exists_extension_norm_eq_of_isClosedEmbedding, hf.measurableEmbedding, integral_map, map_comap, measurableEmbedding, tendsto_iff_forall_integral_tendsto, toMeasure_mk
-/
lemma _root_.Topology.IsClosedEmbedding.continuousOn_comap_finiteMeasure [NormalSpace Ω']
    {f : Ω -> Ω'} (hf : IsClosedEmbedding f) :
    ContinuousOn (fun (μ : FiniteMeasure Ω') => μ.comap f) {μ | μ (range f)ᶜ = 0} := by
  intro μ hμ
  simp only [ContinuousWithinAt]
  rw [tendsto_iff_forall_integral_tendsto]
  intro g
  obtain ⟨g', -, hg'⟩ : exists g' : Ω' ->ᵇ Real, ‖g'‖ = ‖g‖ ∧ g' ∘ f = g :=
    exists_extension_norm_eq_of_isClosedEmbedding g hf
  have A x : g x = g' (f x) := by change (⇑g) x = (⇑g' ∘ f) x; simp only [hg']
  simp only [comap, toMeasure_mk, A, ← MeasurableEmbedding.integral_map hf.measurableEmbedding,
    MeasurableEmbedding.map_comap hf.measurableEmbedding]
  have B {ν : FiniteMeasure Ω'} (hν : ν (range f)ᶜ = 0) :
      ∫ y in range f, g' y ∂ν = ∫ y, g' y ∂ν := by
    congr
    simp only [null_iff_toMeasure_null] at hν
    exact Measure.restrict_eq_self_of_ae_mem hν
  rw [B hμ]
  have : Tendsto (fun (ν : FiniteMeasure Ω') => ∫ y, g' y ∂ν) (𝓝[{μ | μ (range f)ᶜ = 0}] μ)
      (𝓝 (∫ (y : Ω'), g' y ∂μ)) := by
    rw [nhdsWithin]
    have A : Tendsto (fun (ν : FiniteMeasure Ω') => ∫ y, g' y ∂ν) (𝓝 μ) (𝓝 (∫ (y : Ω'), g' y ∂μ)) :=
      tendsto_iff_forall_integral_tendsto.1 tendsto_id _
    exact Tendsto.mono_left A inf_le_left
  apply Tendsto.congr' _ this
  filter_upwards [self_mem_nhdsWithin] with ν hν using (B hν).symm

end comap

section map

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (ν : FiniteMeasure Ω) (f : Ω -> Ω')
  body: ⟨(ν : Measure Ω).map f, (ν : Measure Ω).isFiniteMeasure_map f⟩

中文:
定义 map
  签名: (ν : 有限测度 Ω) (f : Ω -> Ω')
  定义体: ⟨(ν : Measure Ω).map f, (ν : Measure Ω).isFiniteMeasure_map f⟩

Depends on / 依赖: Measure, isFiniteMeasure_map
-/
noncomputable def map (ν : FiniteMeasure Ω) (f : Ω -> Ω') : FiniteMeasure Ω' :=
  ⟨(ν : Measure Ω).map f, (ν : Measure Ω).isFiniteMeasure_map f⟩

/--
lemma `toMeasure_map` / 引理 `toMeasure_map`

English:
lemma toMeasure_map
  given: (ν : FiniteMeasure Ω) (f : Ω -> Ω')
  proof: rfl

中文:
引理 toMeasure_map
  条件: (ν : 有限测度 Ω) (f : Ω -> Ω')
  证明: rfl
-/
@[simp] lemma toMeasure_map (ν : FiniteMeasure Ω) (f : Ω -> Ω') :
    (ν.map f).toMeasure = ν.toMeasure.map f := rfl

/--
lemma `map_apply'` / 引理 `map_apply'`

English:
lemma map_apply'
  statement: (ν : FiniteMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
  proof: Measure.map_apply_of_aemeasurable f_aemble A_mble

中文:
引理 map_apply'
  结论: (ν : 有限测度 Ω) {f : Ω -> Ω'} (f_aemble : 几乎处处可测 f ν)
  证明: Measure.map_apply_of_aemeasurable f_aemble A_mble

Depends on / 依赖: A_mble, Measure, Measure.map_apply_of_aemeasurable, f_aemble, map_apply_of_aemeasurable
-/
lemma map_apply' (ν : FiniteMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    (ν.map f : Measure Ω') A = (ν : Measure Ω) (f ⁻¹' A) :=
  Measure.map_apply_of_aemeasurable f_aemble A_mble

/--
lemma `map_apply_of_aemeasurable` / 引理 `map_apply_of_aemeasurable`

English:
lemma map_apply_of_aemeasurable
  statement: (ν : FiniteMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
  proof: by
  have key := ν.map_apply' f_aemble A_mble
  exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr key

中文:
引理 map_apply_of_aemeasurable
  结论: (ν : 有限测度 Ω) {f : Ω -> Ω'} (f_aemble : 几乎处处可测 f ν)
  证明: by
  have key := ν.map_apply' f_aemble A_mble
  exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr key

Depends on / 依赖: A_mble, ENNReal, ENNReal.toNNReal_eq_toNNReal_iff, f_aemble, map_apply, measure_ne_top, toNNReal_eq_toNNReal_iff
-/
lemma map_apply_of_aemeasurable (ν : FiniteMeasure Ω) {f : Ω -> Ω'} (f_aemble : AEMeasurable f ν)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    ν.map f A = ν (f ⁻¹' A) := by
  have key := ν.map_apply' f_aemble A_mble
  exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr key

/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  statement: (ν : FiniteMeasure Ω) {f : Ω -> Ω'} (f_mble : Measurable f)
  proof: map_apply_of_aemeasurable ν f_mble.aemeasurable A_mble

中文:
引理 map_apply
  结论: (ν : 有限测度 Ω) {f : Ω -> Ω'} (f_mble : 可测 f)
  证明: map_apply_of_aemeasurable ν f_mble.aemeasurable A_mble

Depends on / 依赖: A_mble, aemeasurable, f_mble, f_mble.aemeasurable, map_apply_of_aemeasurable
-/
lemma map_apply (ν : FiniteMeasure Ω) {f : Ω -> Ω'} (f_mble : Measurable f)
    {A : Set Ω'} (A_mble : MeasurableSet A) :
    ν.map f A = ν (f ⁻¹' A) :=
  map_apply_of_aemeasurable ν f_mble.aemeasurable A_mble

/--
lemma `map_add` / 引理 `map_add`

English:
lemma map_add
  given: {f : Ω -> Ω'} (f_mble : Measurable f) (ν₁ ν₂ : FiniteMeasure Ω)
  proof: by ext; simp [*]

中文:
引理 map_add
  条件: {f : Ω -> Ω'} (f_mble : 可测 f) (ν₁ ν₂ : 有限测度 Ω)
  证明: by ext; simp [*]
-/
@[simp] lemma map_add {f : Ω -> Ω'} (f_mble : Measurable f) (ν₁ ν₂ : FiniteMeasure Ω) :
    (ν₁ + ν₂).map f = ν₁.map f + ν₂.map f := by ext; simp [*]

/--
lemma `map_smul` / 引理 `map_smul`

English:
lemma map_smul
  given: {f : Ω -> Ω'} (c : Real>=0) (ν : FiniteMeasure Ω)
  proof: by
  ext s _
  simp [toMeasure_smul]

中文:
引理 map_smul
  条件: {f : Ω -> Ω'} (c : 实数>=0) (ν : 有限测度 Ω)
  证明: by
  ext s _
  simp [toMeasure_smul]
-/
@[simp] lemma map_smul {f : Ω -> Ω'} (c : Real>=0) (ν : FiniteMeasure Ω) :
    (c • ν).map f = c • (ν.map f) := by
  ext s _
  simp [toMeasure_smul]

/--
Definition of `mapHom` / `mapHom` 的定义

English:
definition mapHom
  signature: {f : Ω -> Ω'} (f_mble : Measurable f)
  body: fun ν => ν.map f
  map_add' := map_add f_mble
  map_smul' := map_smul

中文:
定义 mapHom
  签名: {f : Ω -> Ω'} (f_mble : 可测 f)
  定义体: fun ν => ν.map f
  map_add' := map_add f_mble
  map_smul' := map_smul
-/
noncomputable def mapHom {f : Ω -> Ω'} (f_mble : Measurable f) :
    FiniteMeasure Ω ->ₗ[Real>=0] FiniteMeasure Ω' where
  toFun := fun ν => ν.map f
  map_add' := map_add f_mble
  map_smul' := map_smul

/--
lemma `mass_map_le` / 引理 `mass_map_le`

English:
lemma mass_map_le
  given: (f : Ω -> Ω') (μ : FiniteMeasure Ω)
  statement: (μ.map f).mass <= μ.mass
  proof: by
  simp only [mass, coeFn_def, toMeasure_map, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  by_cases hf : AEMeasurable f μ
  · rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_mono (subset_univ _)
  · simp [Measure.map_of_not_aemeasurable hf]

中文:
引理 mass_map_le
  条件: (f : Ω -> Ω') (μ : 有限测度 Ω)
  结论: (μ.map f).mass <= μ.mass
  证明: by
  simp only [mass, coeFn_def, toMeasure_map, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  by_cases hf : AEMeasurable f μ
  · rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_mono (subset_univ _)
  · simp [Measure.map_of_not_aemeasurable hf]

Depends on / 依赖: AEMeasurable, ENNReal, ENNReal.toNNReal_le_toNNReal, MeasurableSet, MeasurableSet.univ, Measure, Measure.map_apply_of_aemeasurable, Measure.map_of_not_aemeasurable, coeFn_def, map_apply_of_aemeasurable, map_of_not_aemeasurable, measure_mono, measure_ne_top, ne_eq, not_false_eq_true, subset_univ, toMeasure_map, toNNReal_le_toNNReal
-/
lemma mass_map_le (f : Ω -> Ω') (μ : FiniteMeasure Ω) : (μ.map f).mass <= μ.mass := by
  simp only [mass, coeFn_def, toMeasure_map, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  by_cases hf : AEMeasurable f μ
  · rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_mono (subset_univ _)
  · simp [Measure.map_of_not_aemeasurable hf]

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
variable [TopologicalSpace Ω'] [BorelSpace Ω']

/--
lemma `tendsto_map_of_tendsto_of_continuous` / 引理 `tendsto_map_of_tendsto_of_continuous`

English:
lemma tendsto_map_of_tendsto_of_continuous
  statement: {ι : Type*} {L : Filter ι}
  proof: by
  rw [FiniteMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert! lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).measurable

中文:
引理 tendsto_map_of_tendsto_of_continuous
  结论: {ι : 类型} {L : 滤子 ι}
  证明: by
  rw [FiniteMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert! lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).measurable

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, ENNReal, ENNReal.continuous_coe.comp, FiniteMeasure, FiniteMeasure.tendsto_iff_forall_lintegral_tendsto, coe_mk, compContinuous, compContinuous_apply, continuous, continuous_coe, convert, f_cont, f_cont.measurable, g.compContinuous, g.continuous, lintegral_map, measurable, tendsto_iff_forall_lintegral_tendsto
-/
lemma tendsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι}
    (νs : ι -> FiniteMeasure Ω) (ν : FiniteMeasure Ω) (lim : Tendsto νs L (𝓝 ν))
    {f : Ω -> Ω'} (f_cont : Continuous f) :
    Tendsto (fun i => (νs i).map f) L (𝓝 (ν.map f)) := by
  rw [FiniteMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert! lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).measurable

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
the push-forward of finite measures `f* : FiniteMeasure X → FiniteMeasure Y` is continuous
(in the topologies of weak convergence of measures). -/
@[fun_prop]
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
  条件: {f : Ω -> Ω'} (f_cont : 连续 f)
  证明: by
  rw [continuous_iff_continuousAt]
  exact fun _ => tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

Depends on / 依赖: continuousAt, continuous_id, continuous_id.continuousAt, continuous_iff_continuousAt, f_cont, tendsto_map_of_tendsto_of_continuous
-/
lemma continuous_map {f : Ω -> Ω'} (f_cont : Continuous f) :
    Continuous (fun ν => FiniteMeasure.map ν f) := by
  rw [continuous_iff_continuousAt]
  exact fun _ => tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

/--
Definition of `mapCLM` / `mapCLM` 的定义

English:
definition mapCLM
  signature: {f : Ω -> Ω'} (f_cont : Continuous f)
  body: fun ν => ν.map f
  map_add' := map_add f_cont.measurable
  map_smul' := map_smul

中文:
定义 mapCLM
  签名: {f : Ω -> Ω'} (f_cont : 连续 f)
  定义体: fun ν => ν.map f
  map_add' := map_add f_cont.measurable
  map_smul' := map_smul
-/
noncomputable def mapCLM {f : Ω -> Ω'} (f_cont : Continuous f) :
    FiniteMeasure Ω ->L[Real>=0] FiniteMeasure Ω' where
  toFun := fun ν => ν.map f
  map_add' := map_add f_cont.measurable
  map_smul' := map_smul

/--
lemma `Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure` / 引理 `Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure`

English:
lemma Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure
  statement: {Ω : Type*}
  proof: by
  let M : Set (FiniteMeasure Ω') := {μ | μ (range f)ᶜ = 0}
  have A : IsEmbedding (Subtype.val : M -> FiniteMeasure Ω') := IsEmbedding.subtypeVal
  let B : FiniteMeasure Ω ≃ₜ M :=
  { toFun μ := by
      refine ⟨μ.map f, ?_⟩
      simp only [null_iff_toMeasure_null, mem_ofPred_eq, toMeasure_map, M]
      rw [Measure.map_apply hf.continuous.measurable hf.isClosed_range.isOpen_compl.measurableSet]
      simp
    invFun := M.domRestrict (fun μ => μ.comap f)
    continuous_toFun := by fun_prop
    continuous_invFun := by
      rw [← continuousOn_iff_continuous_domRestrict]
      exact hf.continuousOn_comap_finiteMeasure
    left_inv μ := by
      ext s hs
      simp only [Set.domRestrict_apply, toMeasure_comap, toMeasure_map]
      rw [Measure.comap_apply]; rw [Measure.map_apply]; rw [preimage_image_eq]
      · exact hf.injective
      · exact hf.continuous.measurable
      · exact hf.measurableEmbedding.measurableSet_image' hs
      · exact hf.injective
      · exact fun t ht => hf.measurableEmbedding.measurableSet_image' ht
      · exact hs
    right_inv μ := by
      ext s hs
      simp only [Set.domRestrict_apply, toMeasure_map]
      rw [Measure.map_apply hf.continuous.measurable hs]
      simp only [toMeasure_comap]
      rw [Measure.comap_apply _ hf.injective]; rw [image_preimage_eq_inter_range]
      · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
        exact (null_iff_toMeasure_null (↑μ) (range f)ᶜ).mp (by exact μ.2)
      · exact fun t ht => hf.measurableEmbedding.measurableSet_image' ht
      · exact hf.continuous.measurable hs }
  exact A.comp B.isEmbedding

中文:
引理 拓扑.是闭嵌入.isEmbedding_map_finiteMeasure
  结论: {Ω : 类型}
  证明: by
  let M : Set (FiniteMeasure Ω') := {μ | μ (range f)ᶜ = 0}
  have A : IsEmbedding (Subtype.val : M -> FiniteMeasure Ω') := IsEmbedding.subtypeVal
  let B : FiniteMeasure Ω ≃ₜ M :=
  { toFun μ := by
      refine ⟨μ.map f, ?_⟩
      simp only [null_iff_toMeasure_null, mem_ofPred_eq, toMeasure_map, M]
      rw [Measure.map_apply hf.continuous.measurable hf.isClosed_range.isOpen_compl.measurableSet]
      simp
    invFun := M.domRestrict (fun μ => μ.comap f)
    continuous_toFun := by fun_prop
    continuous_invFun := by
      rw [← continuousOn_iff_continuous_domRestrict]
      exact hf.continuousOn_comap_finiteMeasure
    left_inv μ := by
      ext s hs
      simp only [Set.domRestrict_apply, toMeasure_comap, toMeasure_map]
      rw [Measure.comap_apply]; rw [Measure.map_apply]; rw [preimage_image_eq]
      · exact hf.injective
      · exact hf.continuous.measurable
      · exact hf.measurableEmbedding.measurableSet_image' hs
      · exact hf.injective
      · exact fun t ht => hf.measurableEmbedding.measurableSet_image' ht
      · exact hs
    right_inv μ := by
      ext s hs
      simp only [Set.domRestrict_apply, toMeasure_map]
      rw [Measure.map_apply hf.continuous.measurable hs]
      simp only [toMeasure_comap]
      rw [Measure.comap_apply _ hf.injective]; rw [image_preimage_eq_inter_range]
      · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
        exact (null_iff_toMeasure_null (↑μ) (range f)ᶜ).mp (by exact μ.2)
      · exact fun t ht => hf.measurableEmbedding.measurableSet_image' ht
      · exact hf.continuous.measurable hs }
  exact A.comp B.isEmbedding

Depends on / 依赖: FiniteMeasure, IsEmbedding, IsEmbedding.subtypeVal, IsStrictTotalOrder, M.domRestrict, Measure, Measure.map_apply, Subtype, Subtype.val, continuous, continuousOn, continuous_invFun, continuous_toFun, domRestrict, fun_prop, hf.continuous.measurable, hf.isClosed_range.isOpen_compl.measurableSet, invFun, isClosed_range, isOpen_compl
-/
lemma Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω] [NormalSpace Ω']
    (f : Ω -> Ω') (hf : IsClosedEmbedding f) :
    IsEmbedding (fun (μ : FiniteMeasure Ω) => μ.map f) := by
  let M : Set (FiniteMeasure Ω') := {μ | μ (range f)ᶜ = 0}
  have A : IsEmbedding (Subtype.val : M -> FiniteMeasure Ω') := IsEmbedding.subtypeVal
  let B : FiniteMeasure Ω ≃ₜ M :=
  { toFun μ := by
      refine ⟨μ.map f, ?_⟩
      simp only [null_iff_toMeasure_null, mem_ofPred_eq, toMeasure_map, M]
      rw [Measure.map_apply hf.continuous.measurable hf.isClosed_range.isOpen_compl.measurableSet]
      simp
    invFun := M.domRestrict (fun μ => μ.comap f)
    continuous_toFun := by fun_prop
    continuous_invFun := by
      rw [← continuousOn_iff_continuous_domRestrict]
      exact hf.continuousOn_comap_finiteMeasure
    left_inv μ := by
      ext s hs
      simp only [Set.domRestrict_apply, toMeasure_comap, toMeasure_map]
      rw [Measure.comap_apply]; rw [Measure.map_apply]; rw [preimage_image_eq]
      · exact hf.injective
      · exact hf.continuous.measurable
      · exact hf.measurableEmbedding.measurableSet_image' hs
      · exact hf.injective
      · exact fun t ht => hf.measurableEmbedding.measurableSet_image' ht
      · exact hs
    right_inv μ := by
      ext s hs
      simp only [Set.domRestrict_apply, toMeasure_map]
      rw [Measure.map_apply hf.continuous.measurable hs]
      simp only [toMeasure_comap]
      rw [Measure.comap_apply _ hf.injective]; rw [image_preimage_eq_inter_range]
      · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
        exact (null_iff_toMeasure_null (↑μ) (range f)ᶜ).mp (by exact μ.2)
      · exact fun t ht => hf.measurableEmbedding.measurableSet_image' ht
      · exact hf.continuous.measurable hs }
  exact A.comp B.isEmbedding

end map -- section

end FiniteMeasure -- namespace

end MeasureTheory -- namespace
