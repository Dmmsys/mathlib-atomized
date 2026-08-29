/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Measure.PreVariation

/-!
# Total variation for vector-valued measures

This file contains the definition of variation for any `VectorMeasure` in an `ENormedAddCommMonoid`,
in particular, any `NormedAddCommGroup`.

Given a vector-valued measure `μ` we consider the problem of finding a countably additive function
`f` such that, for any set `E`, `‖μ(E)‖ ≤ f(E)`. This suggests defining `f(E)` as the supremum over
partitions `{Eᵢ}` of `E`, of the quantity `∑ᵢ, ‖μ(Eᵢ)‖`. Indeed any solution of the problem must be
not less than this function. It turns out that this function is a measure.

## Main definitions

* `VectorMeasure.variation`: the variation as a `Measure X`
* `VectorMeasure.ennrealVariation`: the variation as a `VectorMeasure X ℝ≥0∞`

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

variable {X : Type*} {mX : MeasurableSpace X}

open scoped ENNReal

namespace MeasureTheory.VectorMeasure

variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

/--
lemma `isSigmaSubadditiveSetFun_enorm` / 引理 `isSigmaSubadditiveSetFun_enorm`

English:
lemma isSigmaSubadditiveSetFun_enorm
  given: (μ : VectorMeasure X V)
  proof: by
  intro s hs
  have hmeas : forall i, MeasurableSet (s i).val := fun i => (s i).prop
  simpa [VectorMeasure.of_disjoint_iUnion hmeas hs] using enorm_tsum_le_tsum_enorm

中文:
引理 isSigmaSubadditiveSetFun_enorm
  条件: (μ : 向量测度 X V)
  证明: by
  intro s hs
  have hmeas : forall i, MeasurableSet (s i).val := fun i => (s i).prop
  simpa [VectorMeasure.of_disjoint_iUnion hmeas hs] using enorm_tsum_le_tsum_enorm

Depends on / 依赖: MeasurableSet, VectorMeasure, VectorMeasure.of_disjoint_iUnion, enorm_tsum_le_tsum_enorm, of_disjoint_iUnion
-/
lemma isSigmaSubadditiveSetFun_enorm (μ : VectorMeasure X V) :
    IsSigmaSubadditiveSetFun (‖μ ·‖ₑ) := by
  intro s hs
  have hmeas : forall i, MeasurableSet (s i).val := fun i => (s i).prop
  simpa [VectorMeasure.of_disjoint_iUnion hmeas hs] using enorm_tsum_le_tsum_enorm

/--
Definition of `variation` / `variation` 的定义

English:
definition variation
  signature: (μ : VectorMeasure X V)
  body: preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp)

中文:
定义 variation
  签名: (μ : 向量测度 X V)
  定义体: preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp)

Depends on / 依赖: isSigmaSubadditiveSetFun_enorm, preVariation
-/
noncomputable def variation (μ : VectorMeasure X V) : Measure X :=
  preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp)

/--
Definition of `ennrealVariation` / `ennrealVariation` 的定义

English:
definition ennrealVariation
  signature: (μ : VectorMeasure X V)
  body: μ.variation.toENNRealVectorMeasure

中文:
定义 ennrealVariation
  签名: (μ : 向量测度 X V)
  定义体: μ.variation.toENNRealVectorMeasure

Depends on / 依赖: toENNRealVectorMeasure, variation, variation.toENNRealVectorMeasure
-/
noncomputable def ennrealVariation (μ : VectorMeasure X V) : VectorMeasure X Real>=0∞ :=
  μ.variation.toENNRealVectorMeasure

end MeasureTheory.VectorMeasure
