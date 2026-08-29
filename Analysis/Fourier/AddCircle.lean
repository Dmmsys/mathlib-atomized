/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!

# Fourier analysis on the additive circle

This file contains basic results on Fourier series for functions on the additive circle
`AddCircle T = ℝ / ℤ • T`.

## Main definitions

* `haarAddCircle`, Haar measure on `AddCircle T`, normalized to have total measure `1`.
  Note that this is not the same normalisation
  as the standard measure defined in `IntervalIntegral.Periodic`,
  so we do not declare it as a `MeasureSpace` instance, to avoid confusion.
* for `n : ℤ`, `fourier n` is the monomial `fun x => exp (2 π i n x / T)`,
  bundled as a continuous map from `AddCircle T` to `ℂ`.
* `fourierBasis` is the Hilbert basis of `Lp ℂ 2 haarAddCircle` given by the images of the
  monomials `fourier n`.
* `fourierCoeff f n`, for `f : AddCircle T → E` (with `E` a complete normed `ℂ`-vector space), is
  the `n`-th Fourier coefficient of `f`, defined as an integral over `AddCircle T`. The lemma
  `fourierCoeff_eq_intervalIntegral` expresses this as an integral over `[a, a + T]` for any real
  `a`.
* `fourierCoeffOn`, for `f : ℝ → E` and `a < b` reals, is the `n`-th Fourier
  coefficient of the unique periodic function of period `b - a` which agrees with `f` on `(a, b]`.
  The lemma `fourierCoeffOn_eq_integral` expresses this as an integral over `[a, b]`.

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(AddCircle T, ℂ)`, i.e. that its `Submodule.topologicalClosure` is `⊤`. This follows
from the Stone-Weierstrass theorem after checking that the span is a subalgebra, is closed under
conjugation, and separates points.

Using this and general theory on approximation of Lᵖ functions by continuous functions, we deduce
(`span_fourierLp_closure_eq_top`) that for any `1 ≤ p < ∞`, the span of the Fourier monomials is
dense in the Lᵖ space of `AddCircle T`. For `p = 2` we show (`orthonormal_fourier`) that the
monomials are also orthonormal, so they form a Hilbert basis for L², which is named as
`fourierBasis`; in particular, for `L²` functions `f`, the Fourier series of `f` converges to `f`
in the `L²` topology (`hasSum_fourier_series_L2`). Parseval's identity, `hasSum_sq_fourierCoeff`, is
a direct consequence.

For continuous maps `f : AddCircle T → ℂ`, the theorem
`hasSum_fourier_series_of_summable` states that if the sequence of Fourier
coefficients of `f` is summable, then the Fourier series `∑ (i : ℤ), fourierCoeff f i * fourier i`
converges to `f` in the uniform-convergence topology of `C(AddCircle T, ℂ)`.
-/

@[expose] public section


noncomputable section

open scoped ENNReal ComplexConjugate Real

open TopologicalSpace ContinuousMap MeasureTheory MeasureTheory.Measure Algebra Submodule Set

variable {T : Real}

namespace AddCircle

/-! ### Measure on `AddCircle T`

In this file we use the Haar measure on `AddCircle T` normalised to have total measure 1 (which is
**not** the same as the standard measure defined in `Topology.Instances.AddCircle`). -/

variable [hT : Fact (0 < T)]

/--
Definition of `haarAddCircle` / `haarAddCircle` 的定义

English:
definition haarAddCircle
  signature: : Measure (AddCircle T)
  body: addHaarMeasure ⊤
deriving IsAddHaarMeasure

中文:
定义 haarAddCircle
  签名: : Measure (AddCircle T)
  定义体: addHaarMeasure ⊤
deriving IsAddHaarMeasure

Depends on / 依赖: addHaarMeasure
-/
def haarAddCircle : Measure (AddCircle T) :=
  addHaarMeasure ⊤
deriving IsAddHaarMeasure

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsProbabilityMeasure (@haarAddCircle T _)
  body: IsProbabilityMeasure.mk addHaarMeasure_self

中文:
实例 :
  签名: IsProbabilityMeasure (@haarAddCircle T _)
  定义体: IsProbabilityMeasure.mk addHaarMeasure_self

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.mk, addHaarMeasure_self
-/
instance : IsProbabilityMeasure (@haarAddCircle T _) :=
  IsProbabilityMeasure.mk addHaarMeasure_self

/--
theorem `volume_eq_smul_haarAddCircle` / 定理 `volume_eq_smul_haarAddCircle`

English:
theorem volume_eq_smul_haarAddCircle
  proof: rfl

中文:
定理 volume_eq_smul_haarAddCircle
  证明: rfl
-/
theorem volume_eq_smul_haarAddCircle :
    (volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _) :=
  rfl

/--
lemma `integral_haarAddCircle` / 引理 `integral_haarAddCircle`

English:
lemma integral_haarAddCircle
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [volume_eq_smul_haarAddCircle]; rw [integral_smul_measure]; rw [ENNReal.toReal_ofReal hT.out.le]; rw [inv_smul_smul₀ hT.out.ne']

中文:
引理 integral_haarAddCircle
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: by
  rw [volume_eq_smul_haarAddCircle]; rw [integral_smul_measure]; rw [ENNReal.toReal_ofReal hT.out.le]; rw [inv_smul_smul₀ hT.out.ne']

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, hT.out.le, hT.out.ne, integral_smul_measure, toReal_ofReal, volume_eq_smul_haarAddCircle
-/
lemma integral_haarAddCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : AddCircle T -> E} : ∫ t, f t ∂haarAddCircle = T⁻¹ • ∫ t, f t := by
  rw [volume_eq_smul_haarAddCircle]; rw [integral_smul_measure]; rw [ENNReal.toReal_ofReal hT.out.le]; rw [inv_smul_smul₀ hT.out.ne']

end AddCircle

namespace MeasureTheory

/--
lemma `memLp_haarAddCircle_iff` / 引理 `memLp_haarAddCircle_iff`

English:
lemma memLp_haarAddCircle_iff
  given: [hT : Fact (0 < T)] {f : AddCircle T -> Complex} {p : Real>=0∞}
  proof: by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  have hT' := hT.out
  refine ⟨fun h => h.smul_measure (by finiteness), fun h => ?_⟩
  have := h.smul_measure (c := (ENNReal.ofReal T)⁻¹) (by finiteness)
  rwa [smul_smul, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_smul] at this

alia

中文:
引理 memLp_haarAddCircle_iff
  条件: [hT : Fact (0 < T)] {f : AddCircle T -> Complex} {p : 实数>=0∞}
  证明: by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  have hT' := hT.out
  refine ⟨fun h => h.smul_measure (by finiteness), fun h => ?_⟩
  have := h.smul_measure (c := (ENNReal.ofReal T)⁻¹) (by finiteness)
  rwa [smul_smul, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_smul] at this

alia

Depends on / 依赖: AddCircle, AddCircle.volume_eq_smul_haarAddCircle, ENNReal, ENNReal.inv_mul_cancel, ENNReal.ofReal, finiteness, h.smul_measure, hT.out, inv_mul_cancel, ofReal, one_smul, smul_measure, smul_smul, volume_eq_smul_haarAddCircle
-/
lemma memLp_haarAddCircle_iff [hT : Fact (0 < T)] {f : AddCircle T -> Complex} {p : Real>=0∞} :
    MemLp f p AddCircle.haarAddCircle ↔ MemLp f p := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  have hT' := hT.out
  refine ⟨fun h => h.smul_measure (by finiteness), fun h => ?_⟩
  have := h.smul_measure (c := (ENNReal.ofReal T)⁻¹) (by finiteness)
  rwa [smul_smul, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_smul] at this

alias ⟨MemLp.of_haarAddCircle, MemLp.haarAddCircle⟩ := memLp_haarAddCircle_iff

end MeasureTheory

open AddCircle

section Monomials

/--
Definition of `fourier` / `fourier` 的定义

English:
definition fourier
  signature: (n : Int)
  body: toCircle (n • x :)
continuous_toFun := continuous_induced_dom.comp continuous_toCircle.comp continuous_zsmul _

@[simp]

中文:
定义 fourier
  签名: (n : 整数)
  定义体: toCircle (n • x :)
continuous_toFun := continuous_induced_dom.comp continuous_toCircle.comp continuous_zsmul _

@[simp]

Depends on / 依赖: toCircle
-/
def fourier (n : Int) : C(AddCircle T, Complex) where
  toFun x := toCircle (n • x :)
continuous_toFun := continuous_induced_dom.comp continuous_toCircle.comp continuous_zsmul _

@[simp]
/--
theorem `fourier_apply` / 定理 `fourier_apply`

English:
theorem fourier_apply
  given: {n : Int} {x : AddCircle T}
  statement: fourier n x = toCircle (n • x :)
  proof: rfl

中文:
定理 fourier_apply
  条件: {n : 整数} {x : AddCircle T}
  结论: fourier n x = toCircle (n • x :)
  证明: rfl
-/
theorem fourier_apply {n : Int} {x : AddCircle T} : fourier n x = toCircle (n • x :) :=
  rfl

-- simp normal form is `fourier_coe_apply'`
/--
theorem `fourier_coe_apply` / 定理 `fourier_coe_apply`

English:
theorem fourier_coe_apply
  given: {n : Int} {x : Real}
  proof: by
  rw [fourier_apply]; rw [← QuotientAddGroup.mk_zsmul]; rw [toCircle]; rw [Function.Periodic.lift_coe]; rw [Circle.coe_exp]; rw [Complex.ofReal_mul]; rw [Complex.ofReal_div]; rw [Complex.ofReal_mul]; rw [zsmul_eq_mul]; rw [Complex.ofReal_mul]; rw [Complex.ofReal_intCast]
  norm_num
  congr 1; rin

中文:
定理 fourier_coe_apply
  条件: {n : 整数} {x : 实数}
  证明: by
  rw [fourier_apply]; rw [← QuotientAddGroup.mk_zsmul]; rw [toCircle]; rw [Function.Periodic.lift_coe]; rw [Circle.coe_exp]; rw [Complex.ofReal_mul]; rw [Complex.ofReal_div]; rw [Complex.ofReal_mul]; rw [zsmul_eq_mul]; rw [Complex.ofReal_mul]; rw [Complex.ofReal_intCast]
  norm_num
  congr 1; rin

Depends on / 依赖: Circle, Circle.coe_exp, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_mul, Function, Function.Periodic.lift_coe, Periodic, QuotientAddGroup, QuotientAddGroup.mk_zsmul, coe_exp, fourier_apply, lift_coe, mk_zsmul, ofReal_div, ofReal_intCast, ofReal_mul, toCircle, zsmul_eq_mul
-/
theorem fourier_coe_apply {n : Int} {x : Real} :
    fourier n (x : AddCircle T) = Complex.exp (2 * π * Complex.I * n * x / T) := by
  rw [fourier_apply]; rw [← QuotientAddGroup.mk_zsmul]; rw [toCircle]; rw [Function.Periodic.lift_coe]; rw [Circle.coe_exp]; rw [Complex.ofReal_mul]; rw [Complex.ofReal_div]; rw [Complex.ofReal_mul]; rw [zsmul_eq_mul]; rw [Complex.ofReal_mul]; rw [Complex.ofReal_intCast]
  norm_num
  congr 1; ring

@[simp]
/--
theorem `fourier_coe_apply'` / 定理 `fourier_coe_apply'`

English:
theorem fourier_coe_apply'
  given: {n : Int} {x : Real}
  proof: by
  rw [← fourier_apply]; exact fourier_coe_apply

中文:
定理 fourier_coe_apply'
  条件: {n : 整数} {x : 实数}
  证明: by
  rw [← fourier_apply]; exact fourier_coe_apply

Depends on / 依赖: fourier_apply, fourier_coe_apply
-/
theorem fourier_coe_apply' {n : Int} {x : Real} :
    toCircle (n • (x : AddCircle T) :) = Complex.exp (2 * π * Complex.I * n * x / T) := by
  rw [← fourier_apply]; exact fourier_coe_apply

-- simp normal form is `fourier_zero'`
/--
theorem `fourier_zero` / 定理 `fourier_zero`

English:
theorem fourier_zero
  given: {x : AddCircle T}
  statement: fourier 0 x = 1
  proof: by
  simp

中文:
定理 fourier_zero
  条件: {x : AddCircle T}
  结论: fourier 0 x = 1
  证明: by
  simp
-/
theorem fourier_zero {x : AddCircle T} : fourier 0 x = 1 := by
  simp

/--
theorem `fourier_zero'` / 定理 `fourier_zero'`

English:
theorem fourier_zero'
  statement: @toCircle T 0 = (1 : Complex)
  proof: by
  simp

中文:
定理 fourier_zero'
  结论: @toCircle T 0 = (1 : Complex)
  证明: by
  simp
-/
theorem fourier_zero' : @toCircle T 0 = (1 : Complex) := by
  simp

-- simp normal form is *also* `fourier_zero'`
/--
theorem `fourier_eval_zero` / 定理 `fourier_eval_zero`

English:
theorem fourier_eval_zero
  given: (n : Int)
  statement: fourier n (0 : AddCircle T) = 1
  proof: by
  rw [← QuotientAddGroup.mk_zero]; rw [fourier_coe_apply]; rw [Complex.ofReal_zero]; rw [mul_zero]; rw [zero_div]; rw [Complex.exp_zero]

中文:
定理 fourier_eval_zero
  条件: (n : 整数)
  结论: fourier n (0 : AddCircle T) = 1
  证明: by
  rw [← QuotientAddGroup.mk_zero]; rw [fourier_coe_apply]; rw [Complex.ofReal_zero]; rw [mul_zero]; rw [zero_div]; rw [Complex.exp_zero]

Depends on / 依赖: Complex.exp_zero, Complex.ofReal_zero, QuotientAddGroup, QuotientAddGroup.mk_zero, exp_zero, fourier_coe_apply, mk_zero, mul_zero, ofReal_zero, zero_div
-/
theorem fourier_eval_zero (n : Int) : fourier n (0 : AddCircle T) = 1 := by
  rw [← QuotientAddGroup.mk_zero]; rw [fourier_coe_apply]; rw [Complex.ofReal_zero]; rw [mul_zero]; rw [zero_div]; rw [Complex.exp_zero]

/--
theorem `fourier_one` / 定理 `fourier_one`

English:
theorem fourier_one
  given: {x : AddCircle T}
  statement: fourier 1 x = toCircle x
  proof: by rw [fourier_apply, one_zsmul]

中文:
定理 fourier_one
  条件: {x : AddCircle T}
  结论: fourier 1 x = toCircle x
  证明: by rw [fourier_apply, one_zsmul]

Depends on / 依赖: fourier_apply, one_zsmul
-/
theorem fourier_one {x : AddCircle T} : fourier 1 x = toCircle x := by rw [fourier_apply, one_zsmul]

-- simp normal form is `fourier_neg'`
/--
theorem `fourier_neg` / 定理 `fourier_neg`

English:
theorem fourier_neg
  given: {n : Int} {x : AddCircle T}
  statement: fourier (-n) x = conj (fourier n x)
  proof: by
  induction x using QuotientAddGroup.induction_on
  simp_rw [fourier_apply, toCircle]
  rw [← QuotientAddGroup.mk_zsmul]; rw [← QuotientAddGroup.mk_zsmul]
  simp_rw [Function.Periodic.lift_coe, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg,
    neg_smul, mul_neg]

@[simp]

中文:
定理 fourier_neg
  条件: {n : 整数} {x : AddCircle T}
  结论: fourier (-n) x = conj (fourier n x)
  证明: by
  induction x using QuotientAddGroup.induction_on
  simp_rw [fourier_apply, toCircle]
  rw [← QuotientAddGroup.mk_zsmul]; rw [← QuotientAddGroup.mk_zsmul]
  simp_rw [Function.Periodic.lift_coe, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg,
    neg_smul, mul_neg]

@[simp]

Depends on / 依赖: Circle, Circle.coe_inv_eq_conj, Circle.exp_neg, Function, Function.Periodic.lift_coe, Periodic, QuotientAddGroup, QuotientAddGroup.induction_on, QuotientAddGroup.mk_zsmul, coe_inv_eq_conj, exp_neg, fourier_apply, induction_on, lift_coe, mk_zsmul, mul_neg, neg_smul, simp_rw, toCircle
-/
theorem fourier_neg {n : Int} {x : AddCircle T} : fourier (-n) x = conj (fourier n x) := by
  induction x using QuotientAddGroup.induction_on
  simp_rw [fourier_apply, toCircle]
  rw [← QuotientAddGroup.mk_zsmul]; rw [← QuotientAddGroup.mk_zsmul]
  simp_rw [Function.Periodic.lift_coe, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg,
    neg_smul, mul_neg]

@[simp]
/--
theorem `fourier_neg'` / 定理 `fourier_neg'`

English:
theorem fourier_neg'
  given: {n : Int} {x : AddCircle T}
  statement: @toCircle T (-(n • x)) = conj (fourier n x)
  proof: by
  rw [← neg_smul]; rw [← fourier_apply]; exact fourier_neg

中文:
定理 fourier_neg'
  条件: {n : 整数} {x : AddCircle T}
  结论: @toCircle T (-(n • x)) = conj (fourier n x)
  证明: by
  rw [← neg_smul]; rw [← fourier_apply]; exact fourier_neg

Depends on / 依赖: fourier_apply, fourier_neg, neg_smul
-/
theorem fourier_neg' {n : Int} {x : AddCircle T} : @toCircle T (-(n • x)) = conj (fourier n x) := by
  rw [← neg_smul]; rw [← fourier_apply]; exact fourier_neg

-- simp normal form is `fourier_add'`
/--
theorem `fourier_add` / 定理 `fourier_add`

English:
theorem fourier_add
  given: {m n : Int} {x : AddCircle T}
  proof: by
  simp_rw [fourier_apply, add_zsmul, toCircle_add, Circle.coe_mul]

@[simp]

中文:
定理 fourier_add
  条件: {m n : 整数} {x : AddCircle T}
  证明: by
  simp_rw [fourier_apply, add_zsmul, toCircle_add, Circle.coe_mul]

@[simp]

Depends on / 依赖: Circle, Circle.coe_mul, add_zsmul, coe_mul, fourier_apply, simp_rw, toCircle_add
-/
theorem fourier_add {m n : Int} {x : AddCircle T} :
    fourier (m + n) x = fourier m x * fourier n x := by
  simp_rw [fourier_apply, add_zsmul, toCircle_add, Circle.coe_mul]

@[simp]
/--
theorem `fourier_add'` / 定理 `fourier_add'`

English:
theorem fourier_add'
  given: {m n : Int} {x : AddCircle T}
  proof: by
  rw [← fourier_apply]; exact fourier_add

中文:
定理 fourier_add'
  条件: {m n : 整数} {x : AddCircle T}
  证明: by
  rw [← fourier_apply]; exact fourier_add

Depends on / 依赖: fourier_add, fourier_apply
-/
theorem fourier_add' {m n : Int} {x : AddCircle T} :
    toCircle ((m + n) • x :) = fourier m x * fourier n x := by
  rw [← fourier_apply]; exact fourier_add

/--
theorem `fourier_norm` / 定理 `fourier_norm`

English:
theorem fourier_norm
  given: [Fact (0 < T)] (n : Int)
  statement: ‖@fourier T n‖ = 1
  proof: by
  rw [ContinuousMap.norm_eq_iSup_norm]
  have : forall x : AddCircle T, ‖fourier n x‖ = 1 := fun x => Circle.norm_coe _
  simp_rw [this]
  exact ciSup_const

中文:
定理 fourier_norm
  条件: [Fact (0 < T)] (n : 整数)
  结论: ‖@fourier T n‖ = 1
  证明: by
  rw [ContinuousMap.norm_eq_iSup_norm]
  have : forall x : AddCircle T, ‖fourier n x‖ = 1 := fun x => Circle.norm_coe _
  simp_rw [this]
  exact ciSup_const

Depends on / 依赖: AddCircle, Circle, Circle.norm_coe, ContinuousMap, ContinuousMap.norm_eq_iSup_norm, ciSup_const, fourier, norm_coe, norm_eq_iSup_norm, simp_rw
-/
theorem fourier_norm [Fact (0 < T)] (n : Int) : ‖@fourier T n‖ = 1 := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  have : forall x : AddCircle T, ‖fourier n x‖ = 1 := fun x => Circle.norm_coe _
  simp_rw [this]
  exact ciSup_const

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fourier_add_half_inv_index` / 定理 `fourier_add_half_inv_index`

English:
theorem fourier_add_half_inv_index
  given: {n : Int} (hn : n != 0) (hT : 0 < T) (x : AddCircle T)
  proof: by
  rw [fourier_apply]; rw [zsmul_add]; rw [← QuotientAddGroup.mk_zsmul]; rw [toCircle_add]; rw [Metric.unitSphere.coe_mul]
  have : (@toCircle T (n • (T / 2 / n) : Real) : Complex) = -1 := by
    rw [zsmul_eq_mul]; rw [toCircle]; rw [Function.Periodic.lift_coe]; rw [Circle.coe_exp]
    convert Com

中文:
定理 fourier_add_half_inv_index
  条件: {n : 整数} (hn : n != 0) (hT : 0 < T) (x : AddCircle T)
  证明: by
  rw [fourier_apply]; rw [zsmul_add]; rw [← QuotientAddGroup.mk_zsmul]; rw [toCircle_add]; rw [Metric.unitSphere.coe_mul]
  have : (@toCircle T (n • (T / 2 / n) : Real) : Complex) = -1 := by
    rw [zsmul_eq_mul]; rw [toCircle]; rw [Function.Periodic.lift_coe]; rw [Circle.coe_exp]
    convert Com

Depends on / 依赖: Circle, Circle.coe_exp, Complex.exp_pi_mul_I, Function, Function.Periodic.lift_coe, Metric, Metric.unitSphere.coe_mul, Periodic, QuotientAddGroup, QuotientAddGroup.mk_zsmul, coe_exp, coe_mul, convert, exp_pi_mul_I, fourier_apply, lift_coe, mk_zsmul, toCircle, toCircle_add, unitSphere
-/
theorem fourier_add_half_inv_index {n : Int} (hn : n != 0) (hT : 0 < T) (x : AddCircle T) :
    @fourier T n (x + ↑(T / 2 / n)) = -fourier n x := by
  rw [fourier_apply]; rw [zsmul_add]; rw [← QuotientAddGroup.mk_zsmul]; rw [toCircle_add]; rw [Metric.unitSphere.coe_mul]
  have : (@toCircle T (n • (T / 2 / n) : Real) : Complex) = -1 := by
    rw [zsmul_eq_mul]; rw [toCircle]; rw [Function.Periodic.lift_coe]; rw [Circle.coe_exp]
    convert Complex.exp_pi_mul_I
    field_simp
  rw [this]; simp

/--
Definition of `fourierSubalgebra` / `fourierSubalgebra` 的定义

English:
definition fourierSubalgebra
  signature: : StarSubalgebra Complex C(AddCircle T, Complex) where
  body: Algebra.adjoin Complex (range fourier)
  star_mem' := by
    change Algebra.adjoin Complex (range (fourier (T := T))) <=
      star (Algebra.adjoin Complex (range (fourier (T := T))))
    refine adjoin_le ?_
    rintro - ⟨n, rfl⟩
    exact subset_adjoin ⟨-n, ext fun _ => fourier_neg⟩

中文:
定义 fourierSubalgebra
  签名: : StarSubalgebra Complex C(AddCircle T, Complex) where
  定义体: Algebra.adjoin Complex (range fourier)
  star_mem' := by
    change Algebra.adjoin Complex (range (fourier (T := T))) <=
      star (Algebra.adjoin Complex (range (fourier (T := T))))
    refine adjoin_le ?_
    rintro - ⟨n, rfl⟩
    exact subset_adjoin ⟨-n, ext fun _ => fourier_neg⟩

Depends on / 依赖: Algebra, Algebra.adjoin, adjoin, fourier
-/
def fourierSubalgebra : StarSubalgebra Complex C(AddCircle T, Complex) where
  toSubalgebra := Algebra.adjoin Complex (range fourier)
  star_mem' := by
    change Algebra.adjoin Complex (range (fourier (T := T))) <=
      star (Algebra.adjoin Complex (range (fourier (T := T))))
    refine adjoin_le ?_
    rintro - ⟨n, rfl⟩
    exact subset_adjoin ⟨-n, ext fun _ => fourier_neg⟩

/--
theorem `fourierSubalgebra_coe` / 定理 `fourierSubalgebra_coe`

English:
theorem fourierSubalgebra_coe
  proof: by
  apply adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hx
  · ext1 z; exact fourier_zero
  · rintro - - - - ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext1 z
    exact fourier_add

中文:
定理 fourierSubalgebra_coe
  证明: by
  apply adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hx
  · ext1 z; exact fourier_zero
  · rintro - - - - ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext1 z
    exact fourier_add

Depends on / 依赖: Submodule, Submodule.subset_span, Submonoid, Submonoid.closure_induction, Subset, Subset.trans, adjoin_eq_span_of_subset, closure_induction, fourier_add, fourier_zero, subset_span
-/
theorem fourierSubalgebra_coe :
    Subalgebra.toSubmodule (@fourierSubalgebra T).toSubalgebra = span Complex (range (@fourier T)) := by
  apply adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hx
  · ext1 z; exact fourier_zero
  · rintro - - - - ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext1 z
    exact fourier_add

/- a post-port refactor made `fourierSubalgebra` into a `StarSubalgebra`, and eliminated
`conjInvariantSubalgebra` entirely, making this lemma irrelevant. -/

variable [hT : Fact (0 < T)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `fourierSubalgebra_separatesPoints` / 定理 `fourierSubalgebra_separatesPoints`

English:
theorem fourierSubalgebra_separatesPoints
  statement: (@fourierSubalgebra T).SeparatesPoints
  proof: by
  intro x y hxy
  refine ⟨_, ⟨fourier 1, subset_adjoin ⟨1, rfl⟩, rfl⟩, ?_⟩
  dsimp only; rw [fourier_one, fourier_one]
  contrapose hxy
  rw [Subtype.coe_inj] at hxy
  exact injective_toCircle hT.elim.ne' hxy

中文:
定理 fourierSubalgebra_separatesPoints
  结论: (@fourierSubalgebra T).SeparatesPoints
  证明: by
  intro x y hxy
  refine ⟨_, ⟨fourier 1, subset_adjoin ⟨1, rfl⟩, rfl⟩, ?_⟩
  dsimp only; rw [fourier_one, fourier_one]
  contrapose hxy
  rw [Subtype.coe_inj] at hxy
  exact injective_toCircle hT.elim.ne' hxy

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, contrapose, fourier, fourier_one, hT.elim.ne, injective_toCircle, subset_adjoin
-/
theorem fourierSubalgebra_separatesPoints : (@fourierSubalgebra T).SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨fourier 1, subset_adjoin ⟨1, rfl⟩, rfl⟩, ?_⟩
  dsimp only; rw [fourier_one, fourier_one]
  contrapose hxy
  rw [Subtype.coe_inj] at hxy
  exact injective_toCircle hT.elim.ne' hxy

/--
theorem `fourierSubalgebra_closure_eq_top` / 定理 `fourierSubalgebra_closure_eq_top`

English:
theorem fourierSubalgebra_closure_eq_top
  statement: (@fourierSubalgebra T).topologicalClosure = ⊤
  proof: ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints fourierSubalgebra
    fourierSubalgebra_separatesPoints

中文:
定理 fourierSubalgebra_closure_eq_top
  结论: (@fourierSubalgebra T).topologicalClosure = ⊤
  证明: ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints fourierSubalgebra
    fourierSubalgebra_separatesPoints

Depends on / 依赖: ContinuousMap, ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints, fourierSubalgebra, fourierSubalgebra_separatesPoints, starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
-/
theorem fourierSubalgebra_closure_eq_top : (@fourierSubalgebra T).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints fourierSubalgebra
    fourierSubalgebra_separatesPoints

/--
theorem `span_fourier_closure_eq_top` / 定理 `span_fourier_closure_eq_top`

English:
theorem span_fourier_closure_eq_top
  statement: (span Complex (range <| @fourier T)).topologicalClosure = ⊤
  proof: by
  rw [← fourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    fourierSubalgebra_closure_eq_top

中文:
定理 span_fourier_closure_eq_top
  结论: (span Complex (range <| @fourier T)).topologicalClosure = ⊤
  证明: by
  rw [← fourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    fourierSubalgebra_closure_eq_top

Depends on / 依赖: StarSubalgebra, StarSubalgebra.toSubalgebra, Subalgebra, Subalgebra.toSubmodule, congr_arg, fourierSubalgebra_closure_eq_top, fourierSubalgebra_coe, toSubalgebra, toSubmodule
-/
theorem span_fourier_closure_eq_top : (span Complex (range <| @fourier T)).topologicalClosure = ⊤ := by
  rw [← fourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    fourierSubalgebra_closure_eq_top

/--
Definition of `fourierLp` / `fourierLp` 的定义

English:
abbreviation fourierLp
  signature: (p : Real>=0∞) [Fact (1 <= p)] (n : Int)
  body: toLp (E := Complex) p haarAddCircle Complex (fourier n)

中文:
缩写 fourierLp
  签名: (p : 实数>=0∞) [Fact (1 <= p)] (n : 整数)
  定义体: toLp (E := Complex) p haarAddCircle Complex (fourier n)

Depends on / 依赖: fourier, haarAddCircle
-/
abbrev fourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : Int) : Lp Complex p (@haarAddCircle T hT) :=
  toLp (E := Complex) p haarAddCircle Complex (fourier n)

/--
theorem `coeFn_fourierLp` / 定理 `coeFn_fourierLp`

English:
theorem coeFn_fourierLp
  given: (p : Real>=0∞) [Fact (1 <= p)] (n : Int)
  proof: coeFn_toLp haarAddCircle (fourier n)

中文:
定理 coeFn_fourierLp
  条件: (p : 实数>=0∞) [Fact (1 <= p)] (n : 整数)
  证明: coeFn_toLp haarAddCircle (fourier n)

Depends on / 依赖: coeFn_toLp, fourier, haarAddCircle
-/
theorem coeFn_fourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : Int) :
    @fourierLp T hT p _ n =ᵐ[haarAddCircle] fourier n :=
  coeFn_toLp haarAddCircle (fourier n)

/--
theorem `span_fourierLp_closure_eq_top` / 定理 `span_fourierLp_closure_eq_top`

English:
theorem span_fourierLp_closure_eq_top
  given: {p : Real>=0∞} [Fact (1 <= p)] (hp : p != ∞)
  proof: by
  convert!
    (ContinuousMap.toLp_denseRange Complex (@haarAddCircle T hT) Complex hp).topologicalClosure_map_submodule
      span_fourier_closure_eq_top
  rw [map_span]
  unfold fourierLp
  rw [range_comp']
  simp only [ContinuousLinearMap.coe_coe]

中文:
定理 span_fourierLp_closure_eq_top
  条件: {p : 实数>=0∞} [Fact (1 <= p)] (hp : p != ∞)
  证明: by
  convert!
    (ContinuousMap.toLp_denseRange Complex (@haarAddCircle T hT) Complex hp).topologicalClosure_map_submodule
      span_fourier_closure_eq_top
  rw [map_span]
  unfold fourierLp
  rw [range_comp']
  simp only [ContinuousLinearMap.coe_coe]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_coe, ContinuousMap, ContinuousMap.toLp_denseRange, coe_coe, convert, fourierLp, haarAddCircle, map_span, range_comp, span_fourier_closure_eq_top, toLp_denseRange, topologicalClosure_map_submodule
-/
theorem span_fourierLp_closure_eq_top {p : Real>=0∞} [Fact (1 <= p)] (hp : p != ∞) :
    (span Complex (range (@fourierLp T _ p _))).topologicalClosure = ⊤ := by
  convert!
    (ContinuousMap.toLp_denseRange Complex (@haarAddCircle T hT) Complex hp).topologicalClosure_map_submodule
      span_fourier_closure_eq_top
  rw [map_span]
  unfold fourierLp
  rw [range_comp']
  simp only [ContinuousLinearMap.coe_coe]

/--
theorem `orthonormal_fourier` / 定理 `orthonormal_fourier`

English:
theorem orthonormal_fourier
  statement: Orthonormal Complex (@fourierLp T _ 2 _)
  proof: by
  rw [orthonormal_iff_ite]
  intro i j
  rw [ContinuousMap.inner_toLp (@haarAddCircle T hT) (fourier i) (fourier j)]
  simp_rw [← fourier_neg, ← fourier_add]
  split_ifs with h
  · simp [h]
  have hij : j + -i != 0 := by
    exact sub_ne_zero.mpr (Ne.symm h)
  convert!
    integral_eq_zero_of_add

中文:
定理 orthonormal_fourier
  结论: Orthonormal Complex (@fourierLp T _ 2 _)
  证明: by
  rw [orthonormal_iff_ite]
  intro i j
  rw [ContinuousMap.inner_toLp (@haarAddCircle T hT) (fourier i) (fourier j)]
  simp_rw [← fourier_neg, ← fourier_add]
  split_ifs with h
  · simp [h]
  have hij : j + -i != 0 := by
    exact sub_ne_zero.mpr (Ne.symm h)
  convert!
    integral_eq_zero_of_add

Depends on / 依赖: ContinuousMap, ContinuousMap.inner_toLp, Ne.symm, convert, fourier, fourier_add, fourier_add_half_inv_index, fourier_neg, hT.elim, haarAddCircle, inner_toLp, integral_eq_zero_of_add_right_eq_neg, orthonormal_iff_ite, simp_rw, split_ifs, sub_ne_zero, sub_ne_zero.mpr
-/
theorem orthonormal_fourier : Orthonormal Complex (@fourierLp T _ 2 _) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [ContinuousMap.inner_toLp (@haarAddCircle T hT) (fourier i) (fourier j)]
  simp_rw [← fourier_neg, ← fourier_add]
  split_ifs with h
  · simp [h]
  have hij : j + -i != 0 := by
    exact sub_ne_zero.mpr (Ne.symm h)
  convert!
    integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
      (fourier_add_half_inv_index hij hT.elim)

end Monomials

section ScopeHT

-- everything from here on needs `0 < T`
variable [hT : Fact (0 < T)]

section fourierCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

/--
Definition of `fourierCoeff` / `fourierCoeff` 的定义

English:
definition fourierCoeff
  signature: (f : AddCircle T -> E) (n : Int)
  body: ∫ t : AddCircle T, fourier (-n) t • f t ∂haarAddCircle

中文:
定义 fourierCoeff
  签名: (f : AddCircle T -> E) (n : 整数)
  定义体: ∫ t : AddCircle T, fourier (-n) t • f t ∂haarAddCircle

Depends on / 依赖: AddCircle, fourier, haarAddCircle
-/
def fourierCoeff (f : AddCircle T -> E) (n : Int) : E :=
  ∫ t : AddCircle T, fourier (-n) t • f t ∂haarAddCircle

/--
theorem `fourierCoeff_eq_intervalIntegral` / 定理 `fourierCoeff_eq_intervalIntegral`

English:
theorem fourierCoeff_eq_intervalIntegral
  given: (f : AddCircle T -> E) (n : Int) (a : Real)
  proof: by
  have : forall x : Real, @fourier T (-n) x • f x = (fun z : AddCircle T => @fourier T (-n) z • f z) x := by
    intro x; rfl
  simp_rw +singlePass [this]
  rw [fourierCoeff]; rw [AddCircle.intervalIntegral_preimage T a (fun z => _ • _)]; rw [volume_eq_smul_haarAddCircle]; rw [integral_smul_measu

中文:
定理 fourierCoeff_eq_intervalIntegral
  条件: (f : AddCircle T -> E) (n : 整数) (a : 实数)
  证明: by
  have : forall x : Real, @fourier T (-n) x • f x = (fun z : AddCircle T => @fourier T (-n) z • f z) x := by
    intro x; rfl
  simp_rw +singlePass [this]
  rw [fourierCoeff]; rw [AddCircle.intervalIntegral_preimage T a (fun z => _ • _)]; rw [volume_eq_smul_haarAddCircle]; rw [integral_smul_measu

Depends on / 依赖: AddCircle, AddCircle.intervalIntegral_preimage, ENNReal, ENNReal.toReal_ofReal, fourier, fourierCoeff, hT.out.le, hT.out.ne, integral_smul_measure, intervalIntegral_preimage, one_div_mul_cancel, one_smul, simp_rw, singlePass, smul_assoc, smul_eq_mul, toReal_ofReal, volume_eq_smul_haarAddCircle
-/
theorem fourierCoeff_eq_intervalIntegral (f : AddCircle T -> E) (n : Int) (a : Real) :
    fourierCoeff f n = (1 / T) • ∫ x in a..a + T, @fourier T (-n) x • f x := by
  have : forall x : Real, @fourier T (-n) x • f x = (fun z : AddCircle T => @fourier T (-n) z • f z) x := by
    intro x; rfl
  simp_rw +singlePass [this]
  rw [fourierCoeff]; rw [AddCircle.intervalIntegral_preimage T a (fun z => _ • _)]; rw [volume_eq_smul_haarAddCircle]; rw [integral_smul_measure]; rw [ENNReal.toReal_ofReal hT.out.le]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [one_div_mul_cancel hT.out.ne']; rw [one_smul]

/--
theorem `MeasureTheory.Integrable.fourier_smul` / 定理 `MeasureTheory.Integrable.fourier_smul`

English:
theorem MeasureTheory.Integrable.fourier_smul
  statement: {f : AddCircle T -> E}
  proof: by
  apply hf.bdd_smul 1
  · exact (map_continuous (fourier n)).aestronglyMeasurable
  · apply ae_of_all; intro t
    rw [fourier_apply]; rw [Circle.norm_coe]

中文:
定理 MeasureTheory.Integrable.fourier_smul
  结论: {f : AddCircle T -> E}
  证明: by
  apply hf.bdd_smul 1
  · exact (map_continuous (fourier n)).aestronglyMeasurable
  · apply ae_of_all; intro t
    rw [fourier_apply]; rw [Circle.norm_coe]

Depends on / 依赖: Circle, Circle.norm_coe, ae_of_all, aestronglyMeasurable, bdd_smul, fourier, fourier_apply, hf.bdd_smul, map_continuous, norm_coe
-/
theorem MeasureTheory.Integrable.fourier_smul {f : AddCircle T -> E}
    (hf : Integrable f haarAddCircle) (n : Int) :
    Integrable (fun t => fourier n t • f t) haarAddCircle := by
  apply hf.bdd_smul 1
  · exact (map_continuous (fourier n)).aestronglyMeasurable
  · apply ae_of_all; intro t
    rw [fourier_apply]; rw [Circle.norm_coe]

/--
theorem `fourierCoeff.add` / 定理 `fourierCoeff.add`

English:
theorem fourierCoeff.add
  statement: {f g : AddCircle T -> E} (hf : Integrable f haarAddCircle)
  proof: by
  ext x
  simpa [fourierCoeff, -fourier_apply] using integral_add (hf.fourier_smul _) (hg.fourier_smul _)

中文:
定理 fourierCoeff.add
  结论: {f g : AddCircle T -> E} (hf : 整数egrable f haarAddCircle)
  证明: by
  ext x
  simpa [fourierCoeff, -fourier_apply] using integral_add (hf.fourier_smul _) (hg.fourier_smul _)

Depends on / 依赖: fourierCoeff, fourier_apply, fourier_smul, hf.fourier_smul, hg.fourier_smul, integral_add
-/
theorem fourierCoeff.add {f g : AddCircle T -> E} (hf : Integrable f haarAddCircle)
    (hg : Integrable g haarAddCircle) :
    fourierCoeff (f + g) = fourierCoeff f + fourierCoeff g := by
  ext x
  simpa [fourierCoeff, -fourier_apply] using integral_add (hf.fourier_smul _) (hg.fourier_smul _)

/--
theorem `fourierCoeff.sum` / 定理 `fourierCoeff.sum`

English:
theorem fourierCoeff.sum
  statement: {ι : Type*} (s : Finset ι) (f : ι -> AddCircle T -> E)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => ext; simp [fourierCoeff]
  | insert a s ha iha =>
      obtain ⟨hf₁, hf₂⟩ := by simpa using hf
      rw [s.sum_insert ha]; rw [s.sum_insert ha]; rw [fourierCoeff.add hf₁ (integrable_finsetSum' s hf₂)]; rw [iha hf₂]

中文:
定理 fourierCoeff.sum
  结论: {ι : 类型} (s : Finset ι) (f : ι -> AddCircle T -> E)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => ext; simp [fourierCoeff]
  | insert a s ha iha =>
      obtain ⟨hf₁, hf₂⟩ := by simpa using hf
      rw [s.sum_insert ha]; rw [s.sum_insert ha]; rw [fourierCoeff.add hf₁ (integrable_finsetSum' s hf₂)]; rw [iha hf₂]

Depends on / 依赖: Finset, Finset.induction_on, classical, fourierCoeff, fourierCoeff.add, induction_on, insert, integrable_finsetSum, s.sum_insert, sum_insert
-/
theorem fourierCoeff.sum {ι : Type*} (s : Finset ι) (f : ι -> AddCircle T -> E)
    (hf : forall i in s, Integrable (f i) haarAddCircle) :
    fourierCoeff (∑ i in s, f i) = ∑ i in s, fourierCoeff (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext; simp [fourierCoeff]
  | insert a s ha iha =>
      obtain ⟨hf₁, hf₂⟩ := by simpa using hf
      rw [s.sum_insert ha]; rw [s.sum_insert ha]; rw [fourierCoeff.add hf₁ (integrable_finsetSum' s hf₂)]; rw [iha hf₂]


/--
theorem `fourierCoeff.const_smul` / 定理 `fourierCoeff.const_smul`

English:
theorem fourierCoeff.const_smul
  given: (f : AddCircle T -> E) (c : Complex) (n : Int)
  proof: by
  simp_rw [fourierCoeff, Pi.smul_apply, ← smul_assoc, smul_eq_mul, mul_comm, ← smul_eq_mul,
    smul_assoc, integral_smul]

中文:
定理 fourierCoeff.const_smul
  条件: (f : AddCircle T -> E) (c : Complex) (n : 整数)
  证明: by
  simp_rw [fourierCoeff, Pi.smul_apply, ← smul_assoc, smul_eq_mul, mul_comm, ← smul_eq_mul,
    smul_assoc, integral_smul]

Depends on / 依赖: Pi.smul_apply, fourierCoeff, integral_smul, mul_comm, simp_rw, smul_apply, smul_assoc, smul_eq_mul
-/
theorem fourierCoeff.const_smul (f : AddCircle T -> E) (c : Complex) (n : Int) :
    fourierCoeff (c • f :) n = c • fourierCoeff f n := by
  simp_rw [fourierCoeff, Pi.smul_apply, ← smul_assoc, smul_eq_mul, mul_comm, ← smul_eq_mul,
    smul_assoc, integral_smul]

/--
theorem `fourierCoeff.const_mul` / 定理 `fourierCoeff.const_mul`

English:
theorem fourierCoeff.const_mul
  given: (f : AddCircle T -> Complex) (c : Complex) (n : Int)
  proof: fourierCoeff.const_smul f c n

中文:
定理 fourierCoeff.const_mul
  条件: (f : AddCircle T -> Complex) (c : Complex) (n : 整数)
  证明: fourierCoeff.const_smul f c n

Depends on / 依赖: const_smul, fourierCoeff, fourierCoeff.const_smul
-/
theorem fourierCoeff.const_mul (f : AddCircle T -> Complex) (c : Complex) (n : Int) :
    fourierCoeff (fun x => c * f x) n = c * fourierCoeff f n :=
  fourierCoeff.const_smul f c n

/--
lemma `fourierCoeff_congr_ae` / 引理 `fourierCoeff_congr_ae`

English:
lemma fourierCoeff_congr_ae
  statement: {f g : AddCircle T -> E}
  proof: funext fun _ => integral_congr_ae .smul (.refl _ _) h

中文:
引理 fourierCoeff_congr_ae
  结论: {f g : AddCircle T -> E}
  证明: funext fun _ => integral_congr_ae .smul (.refl _ _) h

Depends on / 依赖: integral_congr_ae
-/
lemma fourierCoeff_congr_ae {f g : AddCircle T -> E}
    (h : f =ᵐ[haarAddCircle] g) : fourierCoeff f = fourierCoeff g :=
funext fun _ => integral_congr_ae .smul (.refl _ _) h

/--
Definition of `fourierCoeffOn` / `fourierCoeffOn` 的定义

English:
definition fourierCoeffOn
  signature: {a b : Real} (hab : a < b) (f : Real -> E) (n : Int)
  body: haveI := Fact.mk (by linarith : 0 < b - a)
  fourierCoeff (AddCircle.liftIoc (b - a) a f) n

中文:
定义 fourierCoeffOn
  签名: {a b : 实数} (hab : a < b) (f : 实数 -> E) (n : 整数)
  定义体: haveI := Fact.mk (by linarith : 0 < b - a)
  fourierCoeff (AddCircle.liftIoc (b - a) a f) n

Depends on / 依赖: AddCircle, AddCircle.liftIoc, Fact.mk, fourierCoeff, liftIoc
-/
def fourierCoeffOn {a b : Real} (hab : a < b) (f : Real -> E) (n : Int) : E :=
  haveI := Fact.mk (by linarith : 0 < b - a)
  fourierCoeff (AddCircle.liftIoc (b - a) a f) n

/--
theorem `fourierCoeffOn_eq_integral` / 定理 `fourierCoeffOn_eq_integral`

English:
theorem fourierCoeffOn_eq_integral
  given: {a b : Real} (f : Real -> E) (n : Int) (hab : a < b)
  proof: by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [fourierCoeffOn]; rw [fourierCoeff_eq_intervalIntegral _ _ a]; rw [add_sub]; rw [add_sub_cancel_left]
  congr 1
  simp_rw [intervalIntegral.integral_of_le hab.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [liftIoc_coe_app

中文:
定理 fourierCoeffOn_eq_integral
  条件: {a b : 实数} (f : 实数 -> E) (n : 整数) (hab : a < b)
  证明: by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [fourierCoeffOn]; rw [fourierCoeff_eq_intervalIntegral _ _ a]; rw [add_sub]; rw [add_sub_cancel_left]
  congr 1
  simp_rw [intervalIntegral.integral_of_le hab.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [liftIoc_coe_app

Depends on / 依赖: Fact.mk, add_sub, add_sub_cancel_left, fourierCoeffOn, fourierCoeff_eq_intervalIntegral, hab.le, integral_of_le, intervalIntegral, intervalIntegral.integral_of_le, liftIoc_coe_apply, measurableSet_Ioc, setIntegral_congr_fun, simp_rw
-/
theorem fourierCoeffOn_eq_integral {a b : Real} (f : Real -> E) (n : Int) (hab : a < b) :
    fourierCoeffOn hab f n =
      (1 / (b - a)) • ∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x := by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [fourierCoeffOn]; rw [fourierCoeff_eq_intervalIntegral _ _ a]; rw [add_sub]; rw [add_sub_cancel_left]
  congr 1
  simp_rw [intervalIntegral.integral_of_le hab.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [liftIoc_coe_apply]
  rwa [add_sub, add_sub_cancel_left]

/--
theorem `fourierCoeffOn.const_smul` / 定理 `fourierCoeffOn.const_smul`

English:
theorem fourierCoeffOn.const_smul
  given: {a b : Real} (f : Real -> E) (c : Complex) (n : Int) (hab : a < b)
  proof: by
  have := Fact.mk (by linarith : 0 < b - a)
  apply fourierCoeff.const_smul

中文:
定理 fourierCoeffOn.const_smul
  条件: {a b : 实数} (f : 实数 -> E) (c : Complex) (n : 整数) (hab : a < b)
  证明: by
  have := Fact.mk (by linarith : 0 < b - a)
  apply fourierCoeff.const_smul

Depends on / 依赖: Fact.mk, const_smul, fourierCoeff, fourierCoeff.const_smul
-/
theorem fourierCoeffOn.const_smul {a b : Real} (f : Real -> E) (c : Complex) (n : Int) (hab : a < b) :
    fourierCoeffOn hab (c • f) n = c • fourierCoeffOn hab f n := by
  have := Fact.mk (by linarith : 0 < b - a)
  apply fourierCoeff.const_smul

/--
theorem `fourierCoeffOn.const_mul` / 定理 `fourierCoeffOn.const_mul`

English:
theorem fourierCoeffOn.const_mul
  given: {a b : Real} (f : Real -> Complex) (c : Complex) (n : Int) (hab : a < b)
  proof: fourierCoeffOn.const_smul _ _ _ _

中文:
定理 fourierCoeffOn.const_mul
  条件: {a b : 实数} (f : 实数 -> Complex) (c : Complex) (n : 整数) (hab : a < b)
  证明: fourierCoeffOn.const_smul _ _ _ _

Depends on / 依赖: const_smul, fourierCoeffOn, fourierCoeffOn.const_smul
-/
theorem fourierCoeffOn.const_mul {a b : Real} (f : Real -> Complex) (c : Complex) (n : Int) (hab : a < b) :
    fourierCoeffOn hab (fun x => c * f x) n = c * fourierCoeffOn hab f n :=
  fourierCoeffOn.const_smul _ _ _ _

/--
lemma `fourierCoeffOn_congr_ae` / 引理 `fourierCoeffOn_congr_ae`

English:
lemma fourierCoeffOn_congr_ae
  statement: {a b : Real} (hab : a < b) {f g : Real -> E}
  proof: by
  ext n
  rw [fourierCoeffOn_eq_integral]; rw [fourierCoeffOn_eq_integral]
  congr! 1
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le hab.le]
  filter_upwards [h] with x hx
  rw [hx]

中文:
引理 fourierCoeffOn_congr_ae
  结论: {a b : 实数} (hab : a < b) {f g : 实数 -> E}
  证明: by
  ext n
  rw [fourierCoeffOn_eq_integral]; rw [fourierCoeffOn_eq_integral]
  congr! 1
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le hab.le]
  filter_upwards [h] with x hx
  rw [hx]

Depends on / 依赖: filter_upwards, fourierCoeffOn_eq_integral, hab.le, integral_congr_ae_restrict, intervalIntegral, intervalIntegral.integral_congr_ae_restrict, uIoc_of_le
-/
lemma fourierCoeffOn_congr_ae {a b : Real} (hab : a < b) {f g : Real -> E}
    (h : f =ᵐ[volume.restrict (Ioc a b)] g) :
    fourierCoeffOn hab f = fourierCoeffOn hab g := by
  ext n
  rw [fourierCoeffOn_eq_integral]; rw [fourierCoeffOn_eq_integral]
  congr! 1
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le hab.le]
  filter_upwards [h] with x hx
  rw [hx]

/--
theorem `fourierCoeff_liftIoc_eq` / 定理 `fourierCoeff_liftIoc_eq`

English:
theorem fourierCoeff_liftIoc_eq
  given: {a : Real} (f : Real -> Complex) (n : Int)
  proof: by
  rw [fourierCoeffOn_eq_integral]; rw [fourierCoeff_eq_intervalIntegral]; rw [add_sub_cancel_left a T]
  · congr 1
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
    rw [liftIoc_coe_apply]
    rwa [uIoc_of_le (lt_add_of_pos_right a hT.out).le] at hx

中文:
定理 fourierCoeff_liftIoc_eq
  条件: {a : 实数} (f : 实数 -> Complex) (n : 整数)
  证明: by
  rw [fourierCoeffOn_eq_integral]; rw [fourierCoeff_eq_intervalIntegral]; rw [add_sub_cancel_left a T]
  · congr 1
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
    rw [liftIoc_coe_apply]
    rwa [uIoc_of_le (lt_add_of_pos_right a hT.out).le] at hx

Depends on / 依赖: add_sub_cancel_left, ae_of_all, fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral, hT.out, integral_congr_ae, intervalIntegral, intervalIntegral.integral_congr_ae, liftIoc_coe_apply, lt_add_of_pos_right, uIoc_of_le
-/
theorem fourierCoeff_liftIoc_eq {a : Real} (f : Real -> Complex) (n : Int) :
    fourierCoeff (AddCircle.liftIoc T a f) n =
    fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by
  rw [fourierCoeffOn_eq_integral]; rw [fourierCoeff_eq_intervalIntegral]; rw [add_sub_cancel_left a T]
  · congr 1
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
    rw [liftIoc_coe_apply]
    rwa [uIoc_of_le (lt_add_of_pos_right a hT.out).le] at hx

/--
theorem `fourierCoeff_liftIco_eq` / 定理 `fourierCoeff_liftIco_eq`

English:
theorem fourierCoeff_liftIco_eq
  given: {a : Real} (f : Real -> Complex) (n : Int)
  proof: by
  rw [fourierCoeffOn_eq_integral]; rw [fourierCoeff_eq_intervalIntegral _ _ a]; rw [add_sub_cancel_left a T]
  congr 1
  refine intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right hT.out.le) fun x hx => ?_
  rw [liftIco_coe_apply (Ioo_subset_Ico_self hx)]

中文:
定理 fourierCoeff_liftIco_eq
  条件: {a : 实数} (f : 实数 -> Complex) (n : 整数)
  证明: by
  rw [fourierCoeffOn_eq_integral]; rw [fourierCoeff_eq_intervalIntegral _ _ a]; rw [add_sub_cancel_left a T]
  congr 1
  refine intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right hT.out.le) fun x hx => ?_
  rw [liftIco_coe_apply (Ioo_subset_Ico_self hx)]

Depends on / 依赖: Ioo_subset_Ico_self, add_sub_cancel_left, fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral, hT.out.le, integral_congr_Ioo_of_le, intervalIntegral, intervalIntegral.integral_congr_Ioo_of_le, le_add_of_nonneg_right, liftIco_coe_apply
-/
theorem fourierCoeff_liftIco_eq {a : Real} (f : Real -> Complex) (n : Int) :
    fourierCoeff (AddCircle.liftIco T a f) n =
    fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by
  rw [fourierCoeffOn_eq_integral]; rw [fourierCoeff_eq_intervalIntegral _ _ a]; rw [add_sub_cancel_left a T]
  congr 1
  refine intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right hT.out.le) fun x hx => ?_
  rw [liftIco_coe_apply (Ioo_subset_Ico_self hx)]

end fourierCoeff

section FourierL2

/--
Definition of `fourierBasis` / `fourierBasis` 的定义

English:
definition fourierBasis
  signature: : HilbertBasis Int Complex (Lp Complex 2 <| @haarAddCircle T hT)
  body: HilbertBasis.mk orthonormal_fourier (span_fourierLp_closure_eq_top (by simp)).ge

中文:
定义 fourierBasis
  签名: : HilbertBasis 整数 Complex (Lp Complex 2 <| @haarAddCircle T hT)
  定义体: HilbertBasis.mk orthonormal_fourier (span_fourierLp_closure_eq_top (by simp)).ge

Depends on / 依赖: HilbertBasis, HilbertBasis.mk, orthonormal_fourier, span_fourierLp_closure_eq_top
-/
def fourierBasis : HilbertBasis Int Complex (Lp Complex 2 <| @haarAddCircle T hT) :=
  HilbertBasis.mk orthonormal_fourier (span_fourierLp_closure_eq_top (by simp)).ge

/-- The elements of the Hilbert basis `fourierBasis` are the functions `fourierLp 2`, i.e. the
monomials `fourier n` on the circle considered as elements of `L²`. -/
@[simp]
/--
theorem `coe_fourierBasis` / 定理 `coe_fourierBasis`

English:
theorem coe_fourierBasis
  statement: ⇑(@fourierBasis T hT) = @fourierLp T hT 2 _
  proof: HilbertBasis.coe_mk _ _

中文:
定理 coe_fourierBasis
  结论: ⇑(@fourierBasis T hT) = @fourierLp T hT 2 _
  证明: HilbertBasis.coe_mk _ _

Depends on / 依赖: HilbertBasis, HilbertBasis.coe_mk, coe_mk
-/
theorem coe_fourierBasis : ⇑(@fourierBasis T hT) = @fourierLp T hT 2 _ :=
  HilbertBasis.coe_mk _ _

/--
theorem `fourierBasis_repr` / 定理 `fourierBasis_repr`

English:
theorem fourierBasis_repr
  given: (f : Lp Complex 2 <| @haarAddCircle T hT) (i : Int)
  proof: by
  trans ∫ t : AddCircle T, conj ((@fourierLp T hT 2 _ i : AddCircle T -> Complex) t) * f t ∂haarAddCircle
  · rw [fourierBasis.repr_apply_apply f i, MeasureTheory.L2.inner_def, coe_fourierBasis]
    simp only [RCLike.inner_apply']
  · apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 

中文:
定理 fourierBasis_repr
  条件: (f : Lp Complex 2 <| @haarAddCircle T hT) (i : 整数)
  证明: by
  trans ∫ t : AddCircle T, conj ((@fourierLp T hT 2 _ i : AddCircle T -> Complex) t) * f t ∂haarAddCircle
  · rw [fourierBasis.repr_apply_apply f i, MeasureTheory.L2.inner_def, coe_fourierBasis]
    simp only [RCLike.inner_apply']
  · apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 

Depends on / 依赖: AddCircle, MeasureTheory, MeasureTheory.L2.inner_def, RCLike, RCLike.inner_apply, coeFn_fourierLp, coe_fourierBasis, filter_upwards, fourierBasis, fourierBasis.repr_apply_apply, fourierLp, fourier_neg, haarAddCircle, inner_apply, inner_def, integral_congr_ae, repr_apply_apply, smul_eq_mul
-/
theorem fourierBasis_repr (f : Lp Complex 2 <| @haarAddCircle T hT) (i : Int) :
    fourierBasis.repr f i = fourierCoeff f i := by
  trans ∫ t : AddCircle T, conj ((@fourierLp T hT 2 _ i : AddCircle T -> Complex) t) * f t ∂haarAddCircle
  · rw [fourierBasis.repr_apply_apply f i, MeasureTheory.L2.inner_def, coe_fourierBasis]
    simp only [RCLike.inner_apply']
  · apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 i] with _ ht
    rw [ht]; rw [← fourier_neg]; rw [smul_eq_mul]

/--
theorem `hasSum_fourier_series_L2` / 定理 `hasSum_fourier_series_L2`

English:
theorem hasSum_fourier_series_L2
  given: (f : Lp Complex 2 <| @haarAddCircle T hT)
  proof: by
  simp_rw [← fourierBasis_repr]; rw [← coe_fourierBasis]
  exact HilbertBasis.hasSum_repr fourierBasis f

中文:
定理 hasSum_fourier_series_L2
  条件: (f : Lp Complex 2 <| @haarAddCircle T hT)
  证明: by
  simp_rw [← fourierBasis_repr]; rw [← coe_fourierBasis]
  exact HilbertBasis.hasSum_repr fourierBasis f

Depends on / 依赖: HilbertBasis, HilbertBasis.hasSum_repr, coe_fourierBasis, fourierBasis, fourierBasis_repr, hasSum_repr, simp_rw
-/
theorem hasSum_fourier_series_L2 (f : Lp Complex 2 <| @haarAddCircle T hT) :
    HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f := by
  simp_rw [← fourierBasis_repr]; rw [← coe_fourierBasis]
  exact HilbertBasis.hasSum_repr fourierBasis f

/--
theorem `hasSum_sq_fourierCoeff` / 定理 `hasSum_sq_fourierCoeff`

English:
theorem hasSum_sq_fourierCoeff
  given: (f : Lp Complex 2 <| @haarAddCircle T hT)
  proof: by
  simp_rw [← fourierBasis_repr]
  have H₁ : HasSum (fun i => ‖fourierBasis.repr f i‖ ^ 2) (‖fourierBasis.repr f‖ ^ 2) := by
    apply_mod_cast lp.hasSum_norm ?_ (fourierBasis.repr f)
    simp
  have H₂ : ‖fourierBasis.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg RCLike.re (@L2.inner_de

中文:
定理 hasSum_sq_fourierCoeff
  条件: (f : Lp Complex 2 <| @haarAddCircle T hT)
  证明: by
  simp_rw [← fourierBasis_repr]
  have H₁ : HasSum (fun i => ‖fourierBasis.repr f i‖ ^ 2) (‖fourierBasis.repr f‖ ^ 2) := by
    apply_mod_cast lp.hasSum_norm ?_ (fourierBasis.repr f)
    simp
  have H₂ : ‖fourierBasis.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg RCLike.re (@L2.inner_de

Depends on / 依赖: AddCircle, HasSum, L2.inner_def, L2.integrable_inner, RCLike, RCLike.re, congr_arg, fourierBasis, fourierBasis.repr, fourierBasis_repr, hasSum_norm, inner_def, integrable_inner, integral_re, lp.hasSum_norm, norm_sq_eq_re_inner, simp_rw
-/
theorem hasSum_sq_fourierCoeff (f : Lp Complex 2 <| @haarAddCircle T hT) :
    HasSum (fun i => ‖fourierCoeff f i‖ ^ 2) (∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle) := by
  simp_rw [← fourierBasis_repr]
  have H₁ : HasSum (fun i => ‖fourierBasis.repr f i‖ ^ 2) (‖fourierBasis.repr f‖ ^ 2) := by
    apply_mod_cast lp.hasSum_norm ?_ (fourierBasis.repr f)
    simp
  have H₂ : ‖fourierBasis.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg RCLike.re (@L2.inner_def (AddCircle T) Complex Complex _ _ _ _ _ f f)
  rw [← integral_re] at H₃
  · simp only [← norm_sq_eq_re_inner] at H₃
    rwa [H₂, H₃] at H₁
  · exact L2.integrable_inner f f

/--
theorem `tsum_sq_fourierCoeff` / 定理 `tsum_sq_fourierCoeff`

English:
theorem tsum_sq_fourierCoeff
  given: (f : Lp Complex 2 <| @haarAddCircle T hT)
  proof: (hasSum_sq_fourierCoeff _).tsum_eq

中文:
定理 tsum_sq_fourierCoeff
  条件: (f : Lp Complex 2 <| @haarAddCircle T hT)
  证明: (hasSum_sq_fourierCoeff _).tsum_eq

Depends on / 依赖: hasSum_sq_fourierCoeff, tsum_eq
-/
theorem tsum_sq_fourierCoeff (f : Lp Complex 2 <| @haarAddCircle T hT) :
    ∑' i : Int, ‖fourierCoeff f i‖ ^ 2 = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle :=
  (hasSum_sq_fourierCoeff _).tsum_eq

/--
theorem `hasSum_sq_fourierCoeffOn` / 定理 `hasSum_sq_fourierCoeffOn`

English:
theorem hasSum_sq_fourierCoeffOn
  proof: by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [← add_sub_cancel a b] at hL2
  have h := hL2.memLp_liftIoc.haarAddCircle
  convert hasSum_sq_fourierCoeff h.toLp
  · simp [fourierCoeff_congr_ae h.coeFn_toLp, fourierCoeff_liftIoc_eq]
  · nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integra

中文:
定理 hasSum_sq_fourierCoeffOn
  证明: by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [← add_sub_cancel a b] at hL2
  have h := hL2.memLp_liftIoc.haarAddCircle
  convert hasSum_sq_fourierCoeff h.toLp
  · simp [fourierCoeff_congr_ae h.coeFn_toLp, fourierCoeff_liftIoc_eq]
  · nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integra

Depends on / 依赖: AddCircle, AddCircle.integral_haarAddCircle, AddCircle.integral_liftIoc_eq_intervalIntegral, Fact.mk, Function, Function.comp_def, add_sub_cancel, coeFn_toLp, comp_def, convert, filter_upwards, fourierCoeff_congr_ae, fourierCoeff_liftIoc_eq, h.coeFn_toLp, h.toLp, hL2.memLp_liftIoc.haarAddCircle, haarAddCircle, hasSum_sq_fourierCoeff, integral_congr_ae, integral_haarAddCircle
-/
theorem hasSum_sq_fourierCoeffOn
    {a b : Real} {f : Real -> Complex} (hab : a < b) (hL2 : MemLp f 2 (volume.restrict (Ioc a b))) :
    HasSum (fun i => ‖fourierCoeffOn hab f i‖ ^ 2) ((b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2) := by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [← add_sub_cancel a b] at hL2
  have h := hL2.memLp_liftIoc.haarAddCircle
  convert hasSum_sq_fourierCoeff h.toLp
  · simp [fourierCoeff_congr_ae h.coeFn_toLp, fourierCoeff_liftIoc_eq]
  · nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integral_liftIoc_eq_intervalIntegral]; rw [← Function.comp_def (f := (‖·‖ ^ 2))]
    simp only [liftIoc_comp_apply, ← AddCircle.integral_haarAddCircle]
    apply integral_congr_ae
    filter_upwards [h.coeFn_toLp] with x hx
    simp [hx]

/--
theorem `tsum_sq_fourierCoeffOn` / 定理 `tsum_sq_fourierCoeffOn`

English:
theorem tsum_sq_fourierCoeffOn
  proof: (hasSum_sq_fourierCoeffOn _ hL2).tsum_eq

中文:
定理 tsum_sq_fourierCoeffOn
  证明: (hasSum_sq_fourierCoeffOn _ hL2).tsum_eq

Depends on / 依赖: hasSum_sq_fourierCoeffOn, tsum_eq
-/
theorem tsum_sq_fourierCoeffOn
    {a b : Real} {f : Real -> Complex} (hab : a < b) (hL2 : MemLp f 2 (volume.restrict (Ioc a b))) :
    ∑' (i : Int), ‖fourierCoeffOn hab f i‖ ^ 2 = (b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2 :=
  (hasSum_sq_fourierCoeffOn _ hL2).tsum_eq

end FourierL2

section Convergence

variable (f : C(AddCircle T, Complex))

/--
theorem `fourierCoeff_toLp` / 定理 `fourierCoeff_toLp`

English:
theorem fourierCoeff_toLp
  given: (n : Int)
  proof: integral_congr_ae (Filter.EventuallyEq.mul (Filter.Eventually.of_forall (by tauto))
    (ContinuousMap.coeFn_toAEEqFun haarAddCircle f))

中文:
定理 fourierCoeff_toLp
  条件: (n : 整数)
  证明: integral_congr_ae (Filter.EventuallyEq.mul (Filter.Eventually.of_forall (by tauto))
    (ContinuousMap.coeFn_toAEEqFun haarAddCircle f))

Depends on / 依赖: fourierCoeff, haarAddCircle
-/
theorem fourierCoeff_toLp (n : Int) :
    fourierCoeff (toLp (E := Complex) 2 haarAddCircle Complex f) n = fourierCoeff f n :=
  integral_congr_ae (Filter.EventuallyEq.mul (Filter.Eventually.of_forall (by tauto))
    (ContinuousMap.coeFn_toAEEqFun haarAddCircle f))

variable {f}

/--
theorem `hasSum_fourier_series_of_summable` / 定理 `hasSum_fourier_series_of_summable`

English:
theorem hasSum_fourier_series_of_summable
  given: (h : Summable (fourierCoeff f))
  proof: by
  have sum_L2 := hasSum_fourier_series_L2 (toLp (E := Complex) 2 haarAddCircle Complex f)
  simp_rw [fourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simp_rw [norm_smul, fourier_norm, mul_one]
  exact h.norm

中文:
定理 hasSum_fourier_series_of_summable
  条件: (h : Summable (fourierCoeff f))
  证明: by
  have sum_L2 := hasSum_fourier_series_L2 (toLp (E := Complex) 2 haarAddCircle Complex f)
  simp_rw [fourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simp_rw [norm_smul, fourier_norm, mul_one]
  exact h.norm

Depends on / 依赖: ContinuousMap, ContinuousMap.hasSum_of_hasSum_Lp, fourierCoeff_toLp, fourier_norm, h.norm, haarAddCircle, hasSum_fourier_series_L2, hasSum_of_hasSum_Lp, mul_one, norm_smul, of_norm, simp_rw, sum_L2
-/
theorem hasSum_fourier_series_of_summable (h : Summable (fourierCoeff f)) :
    HasSum (fun i => fourierCoeff f i • fourier i) f := by
  have sum_L2 := hasSum_fourier_series_L2 (toLp (E := Complex) 2 haarAddCircle Complex f)
  simp_rw [fourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simp_rw [norm_smul, fourier_norm, mul_one]
  exact h.norm

/--
theorem `has_pointwise_sum_fourier_series_of_summable` / 定理 `has_pointwise_sum_fourier_series_of_summable`

English:
theorem has_pointwise_sum_fourier_series_of_summable
  statement: (h : Summable (fourierCoeff f))
  proof: by
  convert! (ContinuousMap.evalCLM Complex x).hasSum (hasSum_fourier_series_of_summable h)

中文:
定理 has_pointwise_sum_fourier_series_of_summable
  结论: (h : Summable (fourierCoeff f))
  证明: by
  convert! (ContinuousMap.evalCLM Complex x).hasSum (hasSum_fourier_series_of_summable h)

Depends on / 依赖: ContinuousMap, ContinuousMap.evalCLM, convert, evalCLM, hasSum, hasSum_fourier_series_of_summable
-/
theorem has_pointwise_sum_fourier_series_of_summable (h : Summable (fourierCoeff f))
    (x : AddCircle T) : HasSum (fun i => fourierCoeff f i • fourier i x) (f x) := by
  convert! (ContinuousMap.evalCLM Complex x).hasSum (hasSum_fourier_series_of_summable h)

end Convergence

end ScopeHT

section computations

/--
theorem `fourierCoeff_fourier` / 定理 `fourierCoeff_fourier`

English:
theorem fourierCoeff_fourier
  given: {T : Real} [hT : Fact (0 < T)] (n : Int)
  proof: by
  ext m
  rw [← fourierCoeff_congr_ae (coeFn_fourierLp 2 n)]; rw [← fourierBasis_repr]; rw [HilbertBasis.repr_apply_apply]; rw [coe_fourierBasis]
  obtain (rfl | hmn) := eq_or_ne m n
  · rw [inner_self_eq_norm_sq_to_K, (orthonormal_fourier (hT := hT)).1 m]; simp
  · rw [(orthonormal_fourier (hT :

中文:
定理 fourierCoeff_fourier
  条件: {T : 实数} [hT : Fact (0 < T)] (n : 整数)
  证明: by
  ext m
  rw [← fourierCoeff_congr_ae (coeFn_fourierLp 2 n)]; rw [← fourierBasis_repr]; rw [HilbertBasis.repr_apply_apply]; rw [coe_fourierBasis]
  obtain (rfl | hmn) := eq_or_ne m n
  · rw [inner_self_eq_norm_sq_to_K, (orthonormal_fourier (hT := hT)).1 m]; simp
  · rw [(orthonormal_fourier (hT :

Depends on / 依赖: HilbertBasis, HilbertBasis.repr_apply_apply, Pi.single, coeFn_fourierLp, coe_fourierBasis, eq_or_ne, fourier, fourierBasis_repr, fourierCoeff_congr_ae, inner_self_eq_norm_sq_to_K, orthonormal_fourier, repr_apply_apply, single
-/
theorem fourierCoeff_fourier {T : Real} [hT : Fact (0 < T)] (n : Int) :
    fourierCoeff (T := T) (fourier n) = Pi.single n 1 := by
  ext m
  rw [← fourierCoeff_congr_ae (coeFn_fourierLp 2 n)]; rw [← fourierBasis_repr]; rw [HilbertBasis.repr_apply_apply]; rw [coe_fourierBasis]
  obtain (rfl | hmn) := eq_or_ne m n
  · rw [inner_self_eq_norm_sq_to_K, (orthonormal_fourier (hT := hT)).1 m]; simp
  · rw [(orthonormal_fourier (hT := hT)).2 hmn]; simp [hmn]

end computations

section deriv

open Complex intervalIntegral

open scoped Interval

variable (T)

/--
theorem `hasDerivAt_fourier` / 定理 `hasDerivAt_fourier`

English:
theorem hasDerivAt_fourier
  given: (n : Int) (x : Real)
  proof: by
  simp_rw [fourier_coe_apply]
  refine (?_ : HasDerivAt (fun y => exp (2 * π * I * n * y / T)) _ _).comp_ofReal
  rw [(fun α β => by ring : forall α β : Complex]; rw [α * exp β = exp β * α)]
  refine (hasDerivAt_exp _).comp (x : Complex) ?_
  convert! hasDerivAt_mul_const (2 * ↑π * I * ↑n / T) us

中文:
定理 hasDerivAt_fourier
  条件: (n : 整数) (x : 实数)
  证明: by
  simp_rw [fourier_coe_apply]
  refine (?_ : HasDerivAt (fun y => exp (2 * π * I * n * y / T)) _ _).comp_ofReal
  rw [(fun α β => by ring : forall α β : Complex]; rw [α * exp β = exp β * α)]
  refine (hasDerivAt_exp _).comp (x : Complex) ?_
  convert! hasDerivAt_mul_const (2 * ↑π * I * ↑n / T) us

Depends on / 依赖: HasDerivAt, comp_ofReal, convert, fourier_coe_apply, hasDerivAt_exp, hasDerivAt_mul_const, simp_rw
-/
theorem hasDerivAt_fourier (n : Int) (x : Real) :
    HasDerivAt (fun y : Real => fourier n (y : AddCircle T))
      (2 * π * I * n / T * fourier n (x : AddCircle T)) x := by
  simp_rw [fourier_coe_apply]
  refine (?_ : HasDerivAt (fun y => exp (2 * π * I * n * y / T)) _ _).comp_ofReal
  rw [(fun α β => by ring : forall α β : Complex]; rw [α * exp β = exp β * α)]
  refine (hasDerivAt_exp _).comp (x : Complex) ?_
  convert! hasDerivAt_mul_const (2 * ↑π * I * ↑n / T) using 1
  ext1 y; ring

/--
theorem `hasDerivAt_fourier_neg` / 定理 `hasDerivAt_fourier_neg`

English:
theorem hasDerivAt_fourier_neg
  given: (n : Int) (x : Real)
  proof: by
  simpa using hasDerivAt_fourier T (-n) x

中文:
定理 hasDerivAt_fourier_neg
  条件: (n : 整数) (x : 实数)
  证明: by
  simpa using hasDerivAt_fourier T (-n) x

Depends on / 依赖: hasDerivAt_fourier
-/
theorem hasDerivAt_fourier_neg (n : Int) (x : Real) :
    HasDerivAt (fun y : Real => fourier (-n) (y : AddCircle T))
      (-2 * π * I * n / T * fourier (-n) (x : AddCircle T)) x := by
  simpa using hasDerivAt_fourier T (-n) x

variable {T}

/--
theorem `has_antideriv_at_fourier_neg` / 定理 `has_antideriv_at_fourier_neg`

English:
theorem has_antideriv_at_fourier_neg
  given: (hT : Fact (0 < T)) {n : Int} (hn : n != 0) (x : Real)
  proof: by
  convert! (hasDerivAt_fourier_neg T n x).div_const (-2 * π * I * n / T) using 1
  · ext1 y; rw [div_div_eq_mul_div]; ring
  · simp [mul_div_cancel_left₀, hn, (Fact.out : 0 < T).ne', Real.pi_pos.ne']

中文:
定理 has_antideriv_at_fourier_neg
  条件: (hT : Fact (0 < T)) {n : 整数} (hn : n != 0) (x : 实数)
  证明: by
  convert! (hasDerivAt_fourier_neg T n x).div_const (-2 * π * I * n / T) using 1
  · ext1 y; rw [div_div_eq_mul_div]; ring
  · simp [mul_div_cancel_left₀, hn, (Fact.out : 0 < T).ne', Real.pi_pos.ne']

Depends on / 依赖: Fact.out, Real.pi_pos.ne, convert, div_const, div_div_eq_mul_div, hasDerivAt_fourier_neg, pi_pos
-/
theorem has_antideriv_at_fourier_neg (hT : Fact (0 < T)) {n : Int} (hn : n != 0) (x : Real) :
    HasDerivAt (fun y : Real => (T : Complex) / (-2 * π * I * n) * fourier (-n) (y : AddCircle T))
      (fourier (-n) (x : AddCircle T)) x := by
  convert! (hasDerivAt_fourier_neg T n x).div_const (-2 * π * I * n / T) using 1
  · ext1 y; rw [div_div_eq_mul_div]; ring
  · simp [mul_div_cancel_left₀, hn, (Fact.out : 0 < T).ne', Real.pi_pos.ne']

/--
theorem `fourierCoeffOn_of_hasDeriv_right` / 定理 `fourierCoeffOn_of_hasDeriv_right`

English:
theorem fourierCoeffOn_of_hasDeriv_right
  statement: {a b : Real} (hab : a < b) {f f' : Real -> Complex}
  proof: by
  rw [← ofReal_sub]
  have hT : Fact (0 < b - a) := ⟨by linarith⟩
  simp_rw [fourierCoeffOn_eq_integral, smul_eq_mul, real_smul, ofReal_div, ofReal_one]
  conv => pattern (occs := 1 2 3) fourier _ _ * _ <;> (rw [mul_comm])
  rw [integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hf
    (fun x _ =>

中文:
定理 fourierCoeffOn_of_hasDeriv_right
  结论: {a b : 实数} (hab : a < b) {f f' : 实数 -> Complex}
  证明: by
  rw [← ofReal_sub]
  have hT : Fact (0 < b - a) := ⟨by linarith⟩
  simp_rw [fourierCoeffOn_eq_integral, smul_eq_mul, real_smul, ofReal_div, ofReal_one]
  conv => pattern (occs := 1 2 3) fourier _ _ * _ <;> (rw [mul_comm])
  rw [integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hf
    (fun x _ =>

Depends on / 依赖: AddCircle, AddCircle.continuo, continuo, continuousAt, continuousWithinAt, fourier, fourierCoeffOn_eq_integral, hasDerivWithinAt, has_antideriv_at_fourier_neg, integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right, map_continuous, mul_comm, ofReal_div, ofReal_one, ofReal_sub, pattern, real_smul, simp_rw, smul_eq_mul
-/
theorem fourierCoeffOn_of_hasDeriv_right {a b : Real} (hab : a < b) {f f' : Real -> Complex}
    {n : Int} (hn : n != 0)
    (hf : ContinuousOn f [[a, b]])
    (hff' : forall x, x in Ioo (min a b) (max a b) -> HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) := by
  rw [← ofReal_sub]
  have hT : Fact (0 < b - a) := ⟨by linarith⟩
  simp_rw [fourierCoeffOn_eq_integral, smul_eq_mul, real_smul, ofReal_div, ofReal_one]
  conv => pattern (occs := 1 2 3) fourier _ _ * _ <;> (rw [mul_comm])
  rw [integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hf
    (fun x _ => has_antideriv_at_fourier_neg hT hn x |>.continuousAt |>.continuousWithinAt) hff'
    (fun x _ => has_antideriv_at_fourier_neg hT hn x |>.hasDerivWithinAt) hf'
    (((map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)).intervalIntegrable _ _)]
  have : forall u v w : Complex, u * ((b - a : Real) / v * w) = (b - a : Real) / v * (u * w) := by intros; ring
  conv in intervalIntegral _ _ _ _ => congr; ext; rw [this]
  rw [(by ring : ((b - a : Real) : Complex) / (-2 * π * I * n) = ((b - a : Real) : Complex) * (1 / (-2 * π * I * n)))]
  have s2 : (b : AddCircle (b - a)) = (a : AddCircle (b - a)) := by
    simpa using coe_add_period (b - a) a
  rw [s2]; rw [intervalIntegral.integral_const_mul]; rw [← sub_mul]; rw [mul_sub]; rw [mul_sub]
  congr 1
  · conv_lhs => rw [mul_comm, mul_div, mul_one]
    rw [div_eq_iff (ofReal_ne_zero.mpr hT.out.ne')]
    ring
  · ring

/--
theorem `fourierCoeffOn_of_hasDerivAt_Ioo` / 定理 `fourierCoeffOn_of_hasDerivAt_Ioo`

English:
theorem fourierCoeffOn_of_hasDerivAt_Ioo
  statement: {a b : Real} (hab : a < b) {f f' : Real -> Complex}
  proof: fourierCoeffOn_of_hasDeriv_right hab hn hf (fun x hx => hff' x hx |>.hasDerivWithinAt) hf'

中文:
定理 fourierCoeffOn_of_hasDerivAt_Ioo
  结论: {a b : 实数} (hab : a < b) {f f' : 实数 -> Complex}
  证明: fourierCoeffOn_of_hasDeriv_right hab hn hf (fun x hx => hff' x hx |>.hasDerivWithinAt) hf'

Depends on / 依赖: fourierCoeffOn_of_hasDeriv_right, hasDerivWithinAt
-/
theorem fourierCoeffOn_of_hasDerivAt_Ioo {a b : Real} (hab : a < b) {f f' : Real -> Complex}
    {n : Int} (hn : n != 0)
    (hf : ContinuousOn f [[a, b]])
    (hff' : forall x, x in Ioo (min a b) (max a b) -> HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) :=
  fourierCoeffOn_of_hasDeriv_right hab hn hf (fun x hx => hff' x hx |>.hasDerivWithinAt) hf'

/--
theorem `fourierCoeffOn_of_hasDerivAt` / 定理 `fourierCoeffOn_of_hasDerivAt`

English:
theorem fourierCoeffOn_of_hasDerivAt
  statement: {a b : Real} (hab : a < b) {f f' : Real -> Complex} {n : Int} (hn : n != 0)
  proof: fourierCoeffOn_of_hasDerivAt_Ioo hab hn
    (fun x hx => hf x hx |>.continuousAt.continuousWithinAt)
    (fun x hx => hf x <| mem_Icc_of_Ioo hx)
    hf'

中文:
定理 fourierCoeffOn_of_hasDerivAt
  结论: {a b : 实数} (hab : a < b) {f f' : 实数 -> Complex} {n : 整数} (hn : n != 0)
  证明: fourierCoeffOn_of_hasDerivAt_Ioo hab hn
    (fun x hx => hf x hx |>.continuousAt.continuousWithinAt)
    (fun x hx => hf x <| mem_Icc_of_Ioo hx)
    hf'

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, fourierCoeffOn_of_hasDerivAt_Ioo, mem_Icc_of_Ioo
-/
theorem fourierCoeffOn_of_hasDerivAt {a b : Real} (hab : a < b) {f f' : Real -> Complex} {n : Int} (hn : n != 0)
    (hf : forall x, x in [[a, b]] -> HasDerivAt f (f' x) x) (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) :=
  fourierCoeffOn_of_hasDerivAt_Ioo hab hn
    (fun x hx => hf x hx |>.continuousAt.continuousWithinAt)
    (fun x hx => hf x <| mem_Icc_of_Ioo hx)
    hf'

end deriv
