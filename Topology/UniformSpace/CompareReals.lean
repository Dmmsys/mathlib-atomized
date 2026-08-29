/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.UniformSpace.AbsoluteValue
public import Mathlib.Topology.UniformSpace.Completion

/-!
# Comparison of Cauchy reals and Bourbaki reals

In `Data.Real.Basic` real numbers are defined using the so called Cauchy construction (although
it is due to Georg Cantor). More precisely, this construction applies to commutative rings equipped
with an absolute value with values in a linear ordered field.

On the other hand, in the `UniformSpace` folder, we construct completions of general uniform
spaces, which allows to construct the Bourbaki real numbers. In this file we build uniformly
continuous bijections from Cauchy reals to Bourbaki reals and back. This is a cross sanity check of
both constructions. Of course those two constructions are variations on the completion idea, simply
with different level of generality. Comparing with Dedekind cuts or quasi-morphisms would be of a
completely different nature.

Note that `MetricSpace/cau_seq_filter` also relates the notions of Cauchy sequences in metric
spaces and Cauchy filters in general uniform spaces, and `MetricSpace/Completion` makes sure
the completion (as a uniform space) of a metric space is a metric space.

Historical note: mathlib used to define real numbers in an intermediate way, using completion
of uniform spaces but extending multiplication in an ad-hoc way.

TODO:
* Upgrade this isomorphism to a topological ring isomorphism.
* Do the same comparison for p-adic numbers

## Implementation notes

The heavy work is done in `Topology/UniformSpace/AbstractCompletion` which provides an abstract
characterization of completions of uniform spaces, and isomorphisms between them. The only work left
here is to prove the uniform space structure coming from the absolute value on ℚ (with values in ℚ,
not referring to ℝ) coincides with the one coming from the metric space structure (which of course
does use ℝ).

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

real numbers, completion, uniform spaces
-/

@[expose] public section


open Set Function Filter CauSeq UniformSpace

/--
theorem `Rat.uniformSpace_eq` / 定理 `Rat.uniformSpace_eq`

English:
theorem Rat.uniformSpace_eq
  proof: by
  ext s
  rw [(AbsoluteValue.hasBasis_uniformity _).mem_iff]; rw [Metric.uniformity_basis_dist_rat.mem_iff]
  simp only [Rat.dist_eq, AbsoluteValue.abs_apply, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_lt,
    _root_.abs_sub_comm]

中文:
定理 有理数.uniformSpace_eq
  证明: by
  ext s
  rw [(AbsoluteValue.hasBasis_uniformity _).mem_iff]; rw [Metric.uniformity_basis_dist_rat.mem_iff]
  simp only [Rat.dist_eq, AbsoluteValue.abs_apply, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_lt,
    _root_.abs_sub_comm]

Depends on / 依赖: AbsoluteValue, AbsoluteValue.abs_apply, AbsoluteValue.hasBasis_uniformity, Metric, Metric.uniformity_basis_dist_rat.mem_iff, Rat.cast_abs, Rat.cast_lt, Rat.cast_sub, Rat.dist_eq, _root_, _root_.abs_sub_comm, abs_apply, abs_sub_comm, cast_abs, cast_lt, cast_sub, dist_eq, hasBasis_uniformity, mem_iff, uniformity_basis_dist_rat
-/
theorem Rat.uniformSpace_eq :
    (AbsoluteValue.abs : AbsoluteValue Rat Rat).uniformSpace = PseudoMetricSpace.toUniformSpace := by
  ext s
  rw [(AbsoluteValue.hasBasis_uniformity _).mem_iff]; rw [Metric.uniformity_basis_dist_rat.mem_iff]
  simp only [Rat.dist_eq, AbsoluteValue.abs_apply, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_lt,
    _root_.abs_sub_comm]

/--
Definition of `rationalCauSeqPkg` / `rationalCauSeqPkg` 的定义

English:
definition rationalCauSeqPkg
  signature: : @AbstractCompletion Rat (@AbsoluteValue.abs Rat _).uniformSpace
  body: @AbstractCompletion.mk
    (space := Real)
    (coe := ((↑) : Rat -> Real))
    (uniformStruct := by infer_instance)
    (complete := by infer_instance)
    (separation := by infer_instance)
    (isUniformInducing := by
      rw [Rat.uniformSpace_eq]
      exact Rat.isUniformEmbedding_coe_real.isUni

中文:
定义 rationalCauSeqPkg
  签名: : @AbstractCompletion 有理数 (@绝对值.abs 有理数 _).uniformSpace
  定义体: @AbstractCompletion.mk
    (space := Real)
    (coe := ((↑) : Rat -> Real))
    (uniformStruct := by infer_instance)
    (complete := by infer_instance)
    (separation := by infer_instance)
    (isUniformInducing := by
      rw [Rat.uniformSpace_eq]
      exact Rat.isUniformEmbedding_coe_real.isUni

Depends on / 依赖: AbstractCompletion, AbstractCompletion.mk, Rat.isDenseEmbedding_coe_real.dense, Rat.isUniformEmbedding_coe_real.isUniformInducing, Rat.uniformSpace_eq, complete, infer_instance, isDenseEmbedding_coe_real, isUniformEmbedding_coe_real, isUniformInducing, separation, uniformSpace_eq, uniformStruct
-/
def rationalCauSeqPkg : @AbstractCompletion Rat (@AbsoluteValue.abs Rat _).uniformSpace :=
  @AbstractCompletion.mk
    (space := Real)
    (coe := ((↑) : Rat -> Real))
    (uniformStruct := by infer_instance)
    (complete := by infer_instance)
    (separation := by infer_instance)
    (isUniformInducing := by
      rw [Rat.uniformSpace_eq]
      exact Rat.isUniformEmbedding_coe_real.isUniformInducing)
    (dense := Rat.isDenseEmbedding_coe_real.dense)

namespace CompareReals

/--
Definition of `Q` / `Q` 的定义

English:
definition Q
  body: Rat deriving CommRing, Inhabited

中文:
定义 Q
  定义体: Rat deriving CommRing, Inhabited

Depends on / 依赖: CommRing, Inhabited, deriving
-/
def Q :=
  Rat deriving CommRing, Inhabited

/--
Instance `uniformSpace` / 实例 `uniformSpace`

English:
instance uniformSpace
  signature: : UniformSpace Q
  body: fast_instance% (@AbsoluteValue.abs Rat _).uniformSpace

中文:
实例 uniformSpace
  签名: : 一致空间 Q
  定义体: fast_instance% (@AbsoluteValue.abs Rat _).uniformSpace

Depends on / 依赖: AbsoluteValue, AbsoluteValue.abs, fast_instance, uniformSpace
-/
instance uniformSpace : UniformSpace Q :=
  fast_instance% (@AbsoluteValue.abs Rat _).uniformSpace

/--
Definition of `BourbakiReal` / `BourbakiReal` 的定义

English:
definition BourbakiReal
  signature: : Type
  body: Completion Q deriving Inhabited

中文:
定义 Bourbaki实数
  签名: : 类型
  定义体: Completion Q deriving Inhabited

Depends on / 依赖: Completion, Inhabited, deriving
-/
def BourbakiReal : Type :=
  Completion Q deriving Inhabited

/--
Instance `Bourbaki.uniformSpace` / 实例 `Bourbaki.uniformSpace`

English:
instance Bourbaki.uniformSpace
  signature: : UniformSpace BourbakiReal
  body: fast_instance% Completion.uniformSpace Q

中文:
实例 Bourbaki.uniformSpace
  签名: : 一致空间 Bourbaki实数
  定义体: fast_instance% Completion.uniformSpace Q

Depends on / 依赖: Completion, Completion.uniformSpace, fast_instance, uniformSpace
-/
instance Bourbaki.uniformSpace : UniformSpace BourbakiReal :=
  fast_instance% Completion.uniformSpace Q

/--
Definition of `bourbakiPkg` / `bourbakiPkg` 的定义

English:
definition bourbakiPkg
  signature: : AbstractCompletion Q
  body: Completion.cPkg

中文:
定义 bourbakiPkg
  签名: : AbstractCompletion Q
  定义体: Completion.cPkg

Depends on / 依赖: Completion, Completion.cPkg
-/
def bourbakiPkg : AbstractCompletion Q :=
  Completion.cPkg

/--
Definition of `compareEquiv` / `compareEquiv` 的定义

English:
definition compareEquiv
  signature: : BourbakiReal ≃ᵤ Real
  body: bourbakiPkg.compareEquiv rationalCauSeqPkg

中文:
定义 compareEquiv
  签名: : Bourbaki实数 ≃ᵤ 实数
  定义体: bourbakiPkg.compareEquiv rationalCauSeqPkg

Depends on / 依赖: bourbakiPkg, bourbakiPkg.compareEquiv, compareEquiv, rationalCauSeqPkg
-/
noncomputable def compareEquiv : BourbakiReal ≃ᵤ Real :=
  bourbakiPkg.compareEquiv rationalCauSeqPkg

/--
theorem `compare_uc` / 定理 `compare_uc`

English:
theorem compare_uc
  statement: UniformContinuous compareEquiv
  proof: bourbakiPkg.uniformContinuous_compareEquiv rationalCauSeqPkg

中文:
定理 compare_uc
  结论: 一致连续 compareEquiv
  证明: bourbakiPkg.uniformContinuous_compareEquiv rationalCauSeqPkg

Depends on / 依赖: bourbakiPkg, bourbakiPkg.uniformContinuous_compareEquiv, rationalCauSeqPkg, uniformContinuous_compareEquiv
-/
theorem compare_uc : UniformContinuous compareEquiv :=
  bourbakiPkg.uniformContinuous_compareEquiv rationalCauSeqPkg

/--
theorem `compare_uc_symm` / 定理 `compare_uc_symm`

English:
theorem compare_uc_symm
  statement: UniformContinuous compareEquiv.symm
  proof: bourbakiPkg.uniformContinuous_compareEquiv_symm rationalCauSeqPkg

中文:
定理 compare_uc_symm
  结论: 一致连续 compareEquiv.symm
  证明: bourbakiPkg.uniformContinuous_compareEquiv_symm rationalCauSeqPkg

Depends on / 依赖: bourbakiPkg, bourbakiPkg.uniformContinuous_compareEquiv_symm, rationalCauSeqPkg, uniformContinuous_compareEquiv_symm
-/
theorem compare_uc_symm : UniformContinuous compareEquiv.symm :=
  bourbakiPkg.uniformContinuous_compareEquiv_symm rationalCauSeqPkg

end CompareReals
