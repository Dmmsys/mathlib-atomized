/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Complex measure

This file defines a complex measure to be a vector measure with codomain `ℂ`.
Then we prove some elementary results about complex measures. In particular, we prove that
a complex measure is always in the form `s + it` where `s` and `t` are signed measures.

## Main definitions

* `MeasureTheory.ComplexMeasure.re`: obtains a signed measure `s` from a complex measure `c`
  such that `s i = (c i).re` for all measurable sets `i`.
* `MeasureTheory.ComplexMeasure.im`: obtains a signed measure `s` from a complex measure `c`
  such that `s i = (c i).im` for all measurable sets `i`.
* `MeasureTheory.SignedMeasure.toComplexMeasure`: given two signed measures `s` and `t`,
  `s.toComplexMeasure t` provides a complex measure of the form `s + it`.
* `MeasureTheory.ComplexMeasure.equivSignedMeasure`: is the equivalence between the complex
  measures and the type of the product of the signed measures with itself.

## Tags

Complex measure
-/

@[expose] public section


noncomputable section

open scoped MeasureTheory ENNReal NNReal

variable {α : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

open VectorMeasure

/--
Definition of `ComplexMeasure` / `ComplexMeasure` 的定义

English:
abbreviation ComplexMeasure
  signature: (α : Type*) [MeasurableSpace α]
  body: VectorMeasure α Complex

中文:
缩写 复测度
  签名: (α : 类型) [可测空间 α]
  定义体: VectorMeasure α Complex

Depends on / 依赖: VectorMeasure
-/
abbrev ComplexMeasure (α : Type*) [MeasurableSpace α] :=
  VectorMeasure α Complex

namespace ComplexMeasure

/-- The real part of a complex measure is a signed measure. -/
@[simps! apply]
/--
Definition of `re` / `re` 的定义

English:
definition re
  signature: : ComplexMeasure α ->ₗ[Real] SignedMeasure α
  body: mapRangeₗ Complex.reCLM Complex.continuous_re

中文:
定义 re
  签名: : 复测度 α ->ₗ[实数] 符号测度 α
  定义体: mapRangeₗ Complex.reCLM Complex.continuous_re

Depends on / 依赖: Complex.continuous_re, Complex.reCLM, continuous_re
-/
def re : ComplexMeasure α ->ₗ[Real] SignedMeasure α :=
  mapRangeₗ Complex.reCLM Complex.continuous_re

/-- The imaginary part of a complex measure is a signed measure. -/
@[simps! apply]
/--
Definition of `im` / `im` 的定义

English:
definition im
  signature: : ComplexMeasure α ->ₗ[Real] SignedMeasure α
  body: mapRangeₗ Complex.imCLM Complex.continuous_im

中文:
定义 im
  签名: : 复测度 α ->ₗ[实数] 符号测度 α
  定义体: mapRangeₗ Complex.imCLM Complex.continuous_im

Depends on / 依赖: Complex.continuous_im, Complex.imCLM, continuous_im
-/
def im : ComplexMeasure α ->ₗ[Real] SignedMeasure α :=
  mapRangeₗ Complex.imCLM Complex.continuous_im

/-- Given `s` and `t` signed measures, `s + it` is a complex measure -/
@[simps!]
/--
Definition of `_root_.MeasureTheory.SignedMeasure.toComplexMeasure` / `_root_.MeasureTheory.SignedMeasure.toComplexMeasure` 的定义

English:
definition _root_.MeasureTheory.SignedMeasure.toComplexMeasure
  signature: (s t : SignedMeasure α)
  body: ⟨s i, t i⟩
  empty' := by rw [s.empty, t.empty]; rfl
  not_measurable' i hi := by rw [s.not_measurable hi, t.not_measurable hi]; rfl
  m_iUnion' _ hf hfdisj := (Complex.hasSum_iff _ _).2 ⟨s.m_iUnion hf hfdisj, t.m_iUnion hf hfdisj⟩

中文:
定义 _root_.测度论.符号测度.toComplexMeasure
  签名: (s t : 符号测度 α)
  定义体: ⟨s i, t i⟩
  empty' := by rw [s.empty, t.empty]; rfl
  not_measurable' i hi := by rw [s.not_measurable hi, t.not_measurable hi]; rfl
  m_iUnion' _ hf hfdisj := (Complex.hasSum_iff _ _).2 ⟨s.m_iUnion hf hfdisj, t.m_iUnion hf hfdisj⟩
-/
def _root_.MeasureTheory.SignedMeasure.toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure α where
  measureOf' i := ⟨s i, t i⟩
  empty' := by rw [s.empty, t.empty]; rfl
  not_measurable' i hi := by rw [s.not_measurable hi, t.not_measurable hi]; rfl
  m_iUnion' _ hf hfdisj := (Complex.hasSum_iff _ _).2 ⟨s.m_iUnion hf hfdisj, t.m_iUnion hf hfdisj⟩

/--
theorem `_root_.MeasureTheory.SignedMeasure.toComplexMeasure_apply` / 定理 `_root_.MeasureTheory.SignedMeasure.toComplexMeasure_apply`

English:
theorem _root_.MeasureTheory.SignedMeasure.toComplexMeasure_apply
  proof: rfl

中文:
定理 _root_.测度论.符号测度.toComplexMeasure_apply
  证明: rfl
-/
theorem _root_.MeasureTheory.SignedMeasure.toComplexMeasure_apply
    {s t : SignedMeasure α} {i : Set α} : s.toComplexMeasure t i = ⟨s i, t i⟩ := rfl

/--
theorem `toComplexMeasure_to_signedMeasure` / 定理 `toComplexMeasure_to_signedMeasure`

English:
theorem toComplexMeasure_to_signedMeasure
  given: (c : ComplexMeasure α)
  proof: rfl

中文:
定理 toComplexMeasure_to_signedMeasure
  条件: (c : 复测度 α)
  证明: rfl
-/
theorem toComplexMeasure_to_signedMeasure (c : ComplexMeasure α) :
    SignedMeasure.toComplexMeasure (ComplexMeasure.re c) (ComplexMeasure.im c) = c := rfl

/--
theorem `_root_.MeasureTheory.SignedMeasure.re_toComplexMeasure` / 定理 `_root_.MeasureTheory.SignedMeasure.re_toComplexMeasure`

English:
theorem _root_.MeasureTheory.SignedMeasure.re_toComplexMeasure
  given: (s t : SignedMeasure α)
  proof: rfl

中文:
定理 _root_.测度论.符号测度.re_toComplexMeasure
  条件: (s t : 符号测度 α)
  证明: rfl
-/
theorem _root_.MeasureTheory.SignedMeasure.re_toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure.re (SignedMeasure.toComplexMeasure s t) = s := rfl

/--
theorem `_root_.MeasureTheory.SignedMeasure.im_toComplexMeasure` / 定理 `_root_.MeasureTheory.SignedMeasure.im_toComplexMeasure`

English:
theorem _root_.MeasureTheory.SignedMeasure.im_toComplexMeasure
  given: (s t : SignedMeasure α)
  proof: rfl

中文:
定理 _root_.测度论.符号测度.im_toComplexMeasure
  条件: (s t : 符号测度 α)
  证明: rfl
-/
theorem _root_.MeasureTheory.SignedMeasure.im_toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure.im (SignedMeasure.toComplexMeasure s t) = t := rfl

/-- The complex measures form an equivalence to the type of pairs of signed measures. -/
@[simps]
/--
Definition of `equivSignedMeasure` / `equivSignedMeasure` 的定义

English:
definition equivSignedMeasure
  signature: : ComplexMeasure α ≃ SignedMeasure α × SignedMeasure α where
  body: ⟨ComplexMeasure.re c, ComplexMeasure.im c⟩
  invFun := fun ⟨s, t⟩ => s.toComplexMeasure t
  left_inv c := c.toComplexMeasure_to_signedMeasure
  right_inv := fun ⟨s, t⟩ => Prod.ext (s.re_toComplexMeasure t) (s.im_toComplexMeasure t)

中文:
定义 equivSignedMeasure
  签名: : 复测度 α ≃ 符号测度 α × 符号测度 α where
  定义体: ⟨ComplexMeasure.re c, ComplexMeasure.im c⟩
  invFun := fun ⟨s, t⟩ => s.toComplexMeasure t
  left_inv c := c.toComplexMeasure_to_signedMeasure
  right_inv := fun ⟨s, t⟩ => Prod.ext (s.re_toComplexMeasure t) (s.im_toComplexMeasure t)

Depends on / 依赖: ComplexMeasure, ComplexMeasure.im, ComplexMeasure.re
-/
def equivSignedMeasure : ComplexMeasure α ≃ SignedMeasure α × SignedMeasure α where
  toFun c := ⟨ComplexMeasure.re c, ComplexMeasure.im c⟩
  invFun := fun ⟨s, t⟩ => s.toComplexMeasure t
  left_inv c := c.toComplexMeasure_to_signedMeasure
  right_inv := fun ⟨s, t⟩ => Prod.ext (s.re_toComplexMeasure t) (s.im_toComplexMeasure t)

section

variable {R : Type*} [Semiring R] [Module R Real]
variable [ContinuousConstSMul R Real] [ContinuousConstSMul R Complex]

set_option backward.isDefEq.respectTransparency false in
/-- The complex measures form a linear isomorphism to the type of pairs of signed measures. -/
@[simps]
/--
Definition of `equivSignedMeasureₗ` / `equivSignedMeasureₗ` 的定义

English:
definition equivSignedMeasureₗ
  signature: : ComplexMeasure α ≃ₗ[R] SignedMeasure α × SignedMeasure α
  body: { equivSignedMeasure with
    map_add' := fun c d => by rfl
    map_smul' := by
      intro r c
      dsimp
      ext
      · simp [Complex.smul_re]
      · simp [Complex.smul_im] }

中文:
定义 equivSignedMeasureₗ
  签名: : 复测度 α ≃ₗ[R] 符号测度 α × 符号测度 α
  定义体: { equivSignedMeasure with
    map_add' := fun c d => by rfl
    map_smul' := by
      intro r c
      dsimp
      ext
      · simp [Complex.smul_re]
      · simp [Complex.smul_im] }

Depends on / 依赖: Complex.smul_im, Complex.smul_re, equivSignedMeasure, map_add, map_smul, smul_im, smul_re
-/
def equivSignedMeasureₗ : ComplexMeasure α ≃ₗ[R] SignedMeasure α × SignedMeasure α :=
  { equivSignedMeasure with
    map_add' := fun c d => by rfl
    map_smul' := by
      intro r c
      dsimp
      ext
      · simp [Complex.smul_re]
      · simp [Complex.smul_im] }

end

set_option backward.isDefEq.respectTransparency false in
/--
theorem `absolutelyContinuous_ennreal_iff` / 定理 `absolutelyContinuous_ennreal_iff`

English:
theorem absolutelyContinuous_ennreal_iff
  given: (c : ComplexMeasure α) (μ : VectorMeasure α Real>=0∞)
  proof: by
  constructor <;> intro h
  · constructor <;> · intro i hi; simp [h hi]
  · intro i hi
    rw [← Complex.re_add_im (c i)]; rw [(_ : (c i).re = 0)]; rw [(_ : (c i).im = 0)]
    exacts [by simp, h.2 hi, h.1 hi]

中文:
定理 absolutelyContinuous_ennreal_iff
  条件: (c : 复测度 α) (μ : 向量测度 α 实数>=0∞)
  证明: by
  constructor <;> intro h
  · constructor <;> · intro i hi; simp [h hi]
  · intro i hi
    rw [← Complex.re_add_im (c i)]; rw [(_ : (c i).re = 0)]; rw [(_ : (c i).im = 0)]
    exacts [by simp, h.2 hi, h.1 hi]

Depends on / 依赖: Complex.re_add_im, exacts, re_add_im
-/
theorem absolutelyContinuous_ennreal_iff (c : ComplexMeasure α) (μ : VectorMeasure α Real>=0∞) :
    c ≪ᵥ μ ↔ ComplexMeasure.re c ≪ᵥ μ ∧ ComplexMeasure.im c ≪ᵥ μ := by
  constructor <;> intro h
  · constructor <;> · intro i hi; simp [h hi]
  · intro i hi
    rw [← Complex.re_add_im (c i)]; rw [(_ : (c i).re = 0)]; rw [(_ : (c i).im = 0)]
    exacts [by simp, h.2 hi, h.1 hi]

end ComplexMeasure

end MeasureTheory
