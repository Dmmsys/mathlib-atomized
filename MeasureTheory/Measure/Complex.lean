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

/-- A `ComplexMeasure` is a `ℂ`-vector measure. -/
/-
**MeasureTheory.ComplexMeasure** 是 Mathlib 中的一个缩写定义，位于命名空间 `MeasureTheory`。
形式化陈述：ComplexMeasure (α : Type*) [MeasurableSpace α]
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `ComplexMeasure` is a `ℂ`-vector measure.
-/
abbrev ComplexMeasure (α : Type*) [MeasurableSpace α] :=
  VectorMeasure α ℂ

namespace ComplexMeasure

/-- The real part of a complex measure is a signed measure. -/
@[simps! apply]
/-
**MeasureTheory.ComplexMeasure.re** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Compl
exMeasure`。
形式化陈述：re : ComplexMeasure α ->ₗ[Real] SignedMeasure α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.continuous_re`：Continuous Complex.re

--- 原说明 ---
The real part of a complex measure is a signed measure.
-/
def re : ComplexMeasure α →ₗ[ℝ] SignedMeasure α :=
  mapRangeₗ Complex.reCLM Complex.continuous_re

/-- The imaginary part of a complex measure is a signed measure. -/
@[simps! apply]
/-
**MeasureTheory.ComplexMeasure.im** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Compl
exMeasure`。
形式化陈述：im : ComplexMeasure α ->ₗ[Real] SignedMeasure α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.continuous_im`：Continuous Complex.im

--- 原说明 ---
The imaginary part of a complex measure is a signed measure.
-/
def im : ComplexMeasure α →ₗ[ℝ] SignedMeasure α :=
  mapRangeₗ Complex.imCLM Complex.continuous_im

/-- Given `s` and `t` signed measures, `s + it` is a complex measure -/
@[simps!]
/-
**MeasureTheory.ComplexMeasure._root_.MeasureTheory.SignedMeasure.toComplexMeasu
re** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.ComplexMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `s` and `t` signed measures, `s + it` is a complex measure
-/
def _root_.MeasureTheory.SignedMeasure.toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure α where
  measureOf' i := ⟨s i, t i⟩
  empty' := by rw [s.empty, t.empty]; rfl
  not_measurable' i hi := by rw [s.not_measurable hi, t.not_measurable hi]; rfl
  m_iUnion' _ hf hfdisj := (Complex.hasSum_iff _ _).2 ⟨s.m_iUnion hf hfdisj, t.m_iUnion hf hfdisj⟩
/-
**MeasureTheory.ComplexMeasure._root_.MeasureTheory.SignedMeasure.toComplexMeasu
re_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.ComplexMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.SignedMeasure.toComplexMeasure_apply
    {s t : SignedMeasure α} {i : Set α} : s.toComplexMeasure t i = ⟨s i, t i⟩ := rfl
/-
**MeasureTheory.ComplexMeasure.toComplexMeasure_to_signedMeasure** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.ComplexMeasure`。
形式化陈述：toComplexMeasure_to_signedMeasure (c : ComplexMeasure α) : SignedMeasure.t
oComplexMeasure (ComplexMeasure.re c) (ComplexMeasure.im c) = c
参数：c : ComplexMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
theorem toComplexMeasure_to_signedMeasure (c : ComplexMeasure α) :
    SignedMeasure.toComplexMeasure (ComplexMeasure.re c) (ComplexMeasure.im c) = c := rfl
/-
**MeasureTheory.ComplexMeasure._root_.MeasureTheory.SignedMeasure.re_toComplexMe
asure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.ComplexMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.SignedMeasure.re_toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure.re (SignedMeasure.toComplexMeasure s t) = s := rfl
/-
**MeasureTheory.ComplexMeasure._root_.MeasureTheory.SignedMeasure.im_toComplexMe
asure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.ComplexMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.SignedMeasure.im_toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure.im (SignedMeasure.toComplexMeasure s t) = t := rfl

/-- The complex measures form an equivalence to the type of pairs of signed measures. -/
@[simps]
/-
**MeasureTheory.ComplexMeasure.equivSignedMeasure** 是 Mathlib 中的一个定义，位于命名空间 `Mea
sureTheory.ComplexMeasure`。
形式化陈述：equivSignedMeasure : ComplexMeasure α ≃ SignedMeasure α × SignedMeasure α 
where toFun c
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ComplexMeasure.toComplexMeasure_to_signedMeasure`：toComple
xMeasure_to_signedMeasure (c : ComplexMeasure α) : SignedMeasure.toComplexMeasur
e (ComplexMeasure.re c) (ComplexMeasure.im c) = c

--- 原说明 ---
The complex measures form an equivalence to the type of pairs of signed measures
.
-/
def equivSignedMeasure : ComplexMeasure α ≃ SignedMeasure α × SignedMeasure α where
  toFun c := ⟨ComplexMeasure.re c, ComplexMeasure.im c⟩
  invFun := fun ⟨s, t⟩ => s.toComplexMeasure t
  left_inv c := c.toComplexMeasure_to_signedMeasure
  right_inv := fun ⟨s, t⟩ => Prod.ext (s.re_toComplexMeasure t) (s.im_toComplexMeasure t)

section

variable {R : Type*} [Semiring R] [Module R ℝ]
variable [ContinuousConstSMul R ℝ] [ContinuousConstSMul R ℂ]

set_option backward.isDefEq.respectTransparency false in
/-- The complex measures form a linear isomorphism to the type of pairs of signed measures. -/
@[simps]
/-
**MeasureTheory.ComplexMeasure.equivSignedMeasure** 是 Mathlib 中的一个定义，位于命名空间 `Mea
sureTheory.ComplexMeasure`。
形式化陈述：equivSignedMeasure : ComplexMeasure α ≃ SignedMeasure α × SignedMeasure α 
where toFun c
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ComplexMeasure.toComplexMeasure_to_signedMeasure`：toComple
xMeasure_to_signedMeasure (c : ComplexMeasure α) : SignedMeasure.toComplexMeasur
e (ComplexMeasure.re c) (ComplexMeasure.im c) = c

--- 原说明 ---
The complex measures form a linear isomorphism to the type of pairs of signed me
asures.
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
/-
**MeasureTheory.ComplexMeasure.absolutelyContinuous_ennreal_iff** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.ComplexMeasure`。
形式化陈述：absolutelyContinuous_ennreal_iff (c : ComplexMeasure α) (μ : VectorMeasure
 α Real>=0∞) : c ≪ᵥ μ ↔ ComplexMeasure.re c ≪ᵥ μ ∧ ComplexMeasure.im c ≪ᵥ μ
参数：c : ComplexMeasure α；μ : VectorMeasure α Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `MeasureTheory.ComplexMeasure.re_apply`：∀ {α : Type u_1} {m : MeasurableS
pace α} (v : MeasureTheory.VectorMeasure α ℂ),   MeasureTheory.ComplexMeasure.re
 v = v.mapRange Complex.reL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `MeasureTheory.ComplexMeasure.im_apply`：∀ {α : Type u_1} {m : MeasurableS
pace α} (v : MeasureTheory.VectorMeasure α ℂ),   MeasureTheory.ComplexMeasure.im
 v = v.mapRange Complex.imL…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem absolutelyContinuous_ennreal_iff (c : ComplexMeasure α) (μ : VectorMeasure α ℝ≥0∞) :
    c ≪ᵥ μ ↔ ComplexMeasure.re c ≪ᵥ μ ∧ ComplexMeasure.im c ≪ᵥ μ := by
  constructor <;> intro h
  · constructor <;> · intro i hi; simp [h hi]
  · intro i hi
    rw [← Complex.re_add_im (c i), (_ : (c i).re = 0), (_ : (c i).im = 0)]
    exacts [by simp, h.2 hi, h.1 hi]

end ComplexMeasure

end MeasureTheory

