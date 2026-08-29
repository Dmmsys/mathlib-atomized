/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.TransferInstance
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.MetricSpace.Completion

/-!
# WithAbs for fields

This extends the `WithAbs` mechanism to fields, providing a type synonym for a field which depends
on an absolute value. This is useful when dealing with several absolute values on the same field.

In particular this allows us to define the completion of a field at a given absolute value.
-/

public section

open Topology

namespace WithAbs

variable {R S : Type*} [Semiring S] [PartialOrder S]

section Field

variable [Field R] {T : Type*} [Field T] (v : AbsoluteValue R S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Field (WithAbs v)
  body: fast_instance% (equiv v).field

中文:
实例 :
  签名: 域 (WithAbs v)
  定义体: fast_instance% (equiv v).field

Depends on / 依赖: fast_instance
-/
instance : Field (WithAbs v) := fast_instance% (equiv v).field

/--
Instance `normedField` / 实例 `normedField`

English:
instance normedField
  signature: (v : AbsoluteValue R Real)
  body: letI := v.toNormedField
  fast_instance% (equiv v).normedField

中文:
实例 normedField
  签名: (v : 绝对值 R 实数)
  定义体: letI := v.toNormedField
  fast_instance% (equiv v).normedField

Depends on / 依赖: fast_instance, normedField, toNormedField, v.toNormedField
-/
noncomputable instance normedField (v : AbsoluteValue R Real) : NormedField (WithAbs v) :=
  letI := v.toNormedField
  fast_instance% (equiv v).normedField

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module
  signature: R T] [FiniteDimensional R T] :
  body: Module.Finite.of_restrictScalars_finite R (WithAbs v) T

中文:
实例 [模
  签名: R T] [有限维 R T] :
  定义体: Module.Finite.of_restrictScalars_finite R (WithAbs v) T

Depends on / 依赖: Finite, Module, Module.Finite.of_restrictScalars_finite, WithAbs, of_restrictScalars_finite
-/
instance [Module R T] [FiniteDimensional R T] :
    FiniteDimensional (WithAbs v) T :=
  Module.Finite.of_restrictScalars_finite R (WithAbs v) T

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module
  signature: T R] [FiniteDimensional T R] :
  body: Module.Finite.equiv (linearEquiv T v).symm

中文:
实例 [模
  签名: T R] [有限维 T R] :
  定义体: Module.Finite.equiv (linearEquiv T v).symm

Depends on / 依赖: Finite, Module, Module.Finite.equiv, linearEquiv
-/
instance [Module T R] [FiniteDimensional T R] :
    FiniteDimensional T (WithAbs v) :=
  Module.Finite.equiv (linearEquiv T v).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: R T] [Algebra.IsSeparable R T] :
  body: .of_equiv_equiv (equiv v).symm (.refl T) (by ext; simp [algebraMap_left_apply])

中文:
实例 [代数
  签名: R T] [代数.是可分 R T] :
  定义体: .of_equiv_equiv (equiv v).symm (.refl T) (by ext; simp [algebraMap_left_apply])

Depends on / 依赖: algebraMap_left_apply, of_equiv_equiv
-/
instance [Algebra R T] [Algebra.IsSeparable R T] :
    Algebra.IsSeparable (WithAbs v) T :=
  .of_equiv_equiv (equiv v).symm (.refl T) (by ext; simp [algebraMap_left_apply])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: T R] [Algebra.IsSeparable T R] :
  body: AlgEquiv.Algebra.isSeparable (algEquiv T v).symm

中文:
实例 [代数
  签名: T R] [代数.是可分 T R] :
  定义体: AlgEquiv.Algebra.isSeparable (algEquiv T v).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.Algebra.isSeparable, Algebra, algEquiv, isSeparable
-/
instance [Algebra T R] [Algebra.IsSeparable T R] :
    Algebra.IsSeparable T (WithAbs v) :=
  AlgEquiv.Algebra.isSeparable (algEquiv T v).symm

/--
lemma `toAbs_div` / 引理 `toAbs_div`

English:
lemma toAbs_div
  given: (x y : R)
  statement: toAbs v (x / y) = toAbs v x / toAbs v y
  proof: rfl

中文:
引理 toAbs_div
  条件: (x y : R)
  结论: toAbs v (x / y) = toAbs v x / toAbs v y
  证明: rfl
-/
@[simp] lemma toAbs_div (x y : R) : toAbs v (x / y) = toAbs v x / toAbs v y := rfl
/--
lemma `ofAbs_div` / 引理 `ofAbs_div`

English:
lemma ofAbs_div
  given: (x y : WithAbs v)
  statement: ofAbs (x / y) = ofAbs x / ofAbs y
  proof: rfl

中文:
引理 ofAbs_div
  条件: (x y : WithAbs v)
  结论: ofAbs (x / y) = ofAbs x / ofAbs y
  证明: rfl
-/
@[simp] lemma ofAbs_div (x y : WithAbs v) : ofAbs (x / y) = ofAbs x / ofAbs y := rfl

/--
lemma `toAbs_inv` / 引理 `toAbs_inv`

English:
lemma toAbs_inv
  given: (x : R)
  statement: toAbs v x⁻¹ = (toAbs v x)⁻¹
  proof: rfl

中文:
引理 toAbs_inv
  条件: (x : R)
  结论: toAbs v x⁻¹ = (toAbs v x)⁻¹
  证明: rfl
-/
@[simp] lemma toAbs_inv (x : R) : toAbs v x⁻¹ = (toAbs v x)⁻¹ := rfl
/--
lemma `ofAbs_inv` / 引理 `ofAbs_inv`

English:
lemma ofAbs_inv
  given: (x : WithAbs v)
  statement: ofAbs (x⁻¹) = (ofAbs x)⁻¹
  proof: rfl

中文:
引理 ofAbs_inv
  条件: (x : WithAbs v)
  结论: ofAbs (x⁻¹) = (ofAbs x)⁻¹
  证明: rfl
-/
@[simp] lemma ofAbs_inv (x : WithAbs v) : ofAbs (x⁻¹) = (ofAbs x)⁻¹ := rfl

/--
theorem `tendsto_one_div_one_add_pow_nhds_one` / 定理 `tendsto_one_div_one_add_pow_nhds_one`

English:
theorem tendsto_one_div_one_add_pow_nhds_one
  given: {v : AbsoluteValue R Real} {a : R} (ha : v a < 1)
  proof: by
  simpa using! inv_one (G := WithAbs v) ▸ (tendsto_inv_iff₀ one_ne_zero).2
    (tendsto_iff_norm_sub_tendsto_zero.2 <| by simpa using! ha)

中文:
定理 tendsto_one_div_one_add_pow_nhds_one
  条件: {v : 绝对值 R 实数} {a : R} (ha : v a < 1)
  证明: by
  simpa using! inv_one (G := WithAbs v) ▸ (tendsto_inv_iff₀ one_ne_zero).2
    (tendsto_iff_norm_sub_tendsto_zero.2 <| by simpa using! ha)

Depends on / 依赖: WithAbs, inv_one, one_ne_zero, tendsto_iff_norm_sub_tendsto_zero
-/
theorem tendsto_one_div_one_add_pow_nhds_one {v : AbsoluteValue R Real} {a : R} (ha : v a < 1) :
    Filter.atTop.Tendsto (fun n => (equiv v).symm (1 / (1 + a ^ n))) (𝓝 1) := by
  simpa using! inv_one (G := WithAbs v) ▸ (tendsto_inv_iff₀ one_ne_zero).2
    (tendsto_iff_norm_sub_tendsto_zero.2 <| by simpa using! ha)

end Field

section CommRing

variable [CommRing R] {T : Type*} [Field T] [Algebra R T] (w : AbsoluteValue T Real)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformContinuousConstSMul R (WithAbs w)
  body: by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _

中文:
实例 :
  签名: 一致连续常数标量乘法 R (WithAbs w)
  定义体: by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _

Depends on / 依赖: Algebra, Algebra.smul_def, Ring.uniformContinuousConstSMul, simp_rw, smul_def, uniformContinuousConstSMul, uniformContinuous_const_smul
-/
instance : UniformContinuousConstSMul R (WithAbs w) where
  uniformContinuous_const_smul r := by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _

end CommRing

/-!
### The completion of a field at an absolute value.
-/

variable {K : Type*} [Field K] {v : AbsoluteValue K Real} {L : Type*} [NormedField L]
  {f : WithAbs v ->+* L}

end WithAbs

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K Real)

/--
Definition of `Completion` / `Completion` 的定义

English:
abbreviation Completion
  body: UniformSpace.Completion (WithAbs v)

中文:
缩写 完备化
  定义体: UniformSpace.Completion (WithAbs v)

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion, WithAbs
-/
abbrev Completion := UniformSpace.Completion (WithAbs v)

namespace Completion

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe K v.Completion
  body: ↑(toAbs v k)

中文:
实例 :
  签名: Coe K v.完备化
  定义体: ↑(toAbs v k)
-/
noncomputable instance : Coe K v.Completion where
  coe k : v.Completion := ↑(toAbs v k)

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v ->+* L} {v}

/--
theorem `locallyCompactSpace` / 定理 `locallyCompactSpace`

English:
theorem locallyCompactSpace
  given: [LocallyCompactSpace L] (h : Isometry f)
  proof: h.completion_extension.isClosedEmbedding.locallyCompactSpace

中文:
定理 locallyCompactSpace
  条件: [局部紧空间 L] (h : 等距 f)
  证明: h.completion_extension.isClosedEmbedding.locallyCompactSpace

Depends on / 依赖: completion_extension, h.completion_extension.isClosedEmbedding.locallyCompactSpace, isClosedEmbedding, locallyCompactSpace
-/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : Isometry f) :
    LocallyCompactSpace v.Completion :=
  h.completion_extension.isClosedEmbedding.locallyCompactSpace

end AbsoluteValue.Completion
