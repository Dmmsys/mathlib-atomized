/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Extension of a linear function from indicators to L1

Given `T : Set α → E →L[ℝ] F` with `DominatedFinMeasAdditive μ T C`, we construct an extension
of `T` to integrable simple functions, which are finite sums of indicators of measurable sets
with finite measure, then to integrable functions, which are limits of integrable simple functions.

The main result is a continuous linear map `(α →₁[μ] E) →L[ℝ] F`.
This extension process is used to define the Bochner integral
in the `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` file,
the conditional expectation of an integrable function
in `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondexpL1.lean`,
and the integral with respect to a vector measure
in `Mathlib/MeasureTheory/VectorMeasure/Integral.lean`.

## Main definitions

- `setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α →₁[μ] E) →L[ℝ] F`: the extension of `T`
  from indicators to L1.
- `setToFun μ T (hT : DominatedFinMeasAdditive μ T C) (f : α → E) : F`: a version of the
  extension which applies to functions (with value 0 if the function is not integrable).

## Properties

For most properties of `setToFun`, we provide two lemmas. One version uses hypotheses valid on
all sets, like `T = T'`, and a second version which uses a primed name uses hypotheses on
measurable sets with finite measure, like `∀ s, MeasurableSet s → μ s < ∞ → T s = T' s`.

The lemmas listed here don't show all hypotheses. Refer to the actual lemmas for details.

Linearity:
- `setToFun_zero_left : setToFun μ 0 hT f = 0`
- `setToFun_add_left : setToFun μ (T + T') _ f = setToFun μ T hT f + setToFun μ T' hT' f`
- `setToFun_smul_left : setToFun μ (fun s ↦ c • (T s)) (hT.smul c) f = c • setToFun μ T hT f`
- `setToFun_zero : setToFun μ T hT (0 : α → E) = 0`
- `setToFun_neg : setToFun μ T hT (-f) = - setToFun μ T hT f`

If `f` and `g` are integrable:
- `setToFun_add : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ T hT g`
- `setToFun_sub : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ T hT g`

If `T` satisfies `∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x`:
- `setToFun_smul : setToFun μ T hT (c • f) = c • setToFun μ T hT f`

Other:
- `setToFun_congr_ae (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g`
- `setToFun_measure_zero (h : μ = 0) : setToFun μ T hT f = 0`

If the space is also an ordered additive group with an order closed topology and `T` is such that
`0 ≤ T s x` for `0 ≤ x`, we also prove order-related properties:
- `setToFun_mono_left (h : ∀ s x, T s x ≤ T' s x) : setToFun μ T hT f ≤ setToFun μ T' hT' f`
- `setToFun_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ setToFun μ T hT f`
- `setToFun_mono (hfg : f ≤ᵐ[μ] g) : setToFun μ T hT f ≤ setToFun μ T hT g`
-/

@[expose] public section


noncomputable section

open scoped Topology NNReal

open Set Filter TopologicalSpace ENNReal

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [NormedAddCommGroup F'] [NormedSpace Real F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ μ' μ'' : Measure α}

namespace L1

open AEEqFun Lp.simpleFunc Lp

namespace SimpleFunc

/--
theorem `norm_eq_sum_mul` / 定理 `norm_eq_sum_mul`

English:
theorem norm_eq_sum_mul
  given: (f : α ->₁ₛ[μ] G)
  proof: by
  rw [norm_toSimpleFunc]; rw [eLpNorm_one_eq_lintegral_enorm]
  have h_eq := SimpleFunc.map_apply (‖·‖ₑ) (toSimpleFunc f)
  simp_rw [← h_eq, measureReal_def]
  rw [SimpleFunc.lintegral_eq_lintegral]; rw [SimpleFunc.map_lintegral]; rw [ENNReal.toReal_sum]
  · congr
    ext1 x
    rw [ENNReal.toRea

中文:
定理 norm_eq_sum_mul
  条件: (f : α ->₁ₛ[μ] G)
  证明: by
  rw [norm_toSimpleFunc]; rw [eLpNorm_one_eq_lintegral_enorm]
  have h_eq := SimpleFunc.map_apply (‖·‖ₑ) (toSimpleFunc f)
  simp_rw [← h_eq, measureReal_def]
  rw [SimpleFunc.lintegral_eq_lintegral]; rw [SimpleFunc.map_lintegral]; rw [ENNReal.toReal_sum]
  · congr
    ext1 x
    rw [ENNReal.toRea

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal, ENNReal.toReal_sum, SimpleFunc, SimpleFunc.integ, SimpleFunc.lintegral_eq_lintegral, SimpleFunc.map_apply, SimpleFunc.map_lintegral, SimpleFunc.measure_preimage_lt_top_of_integrable, eLpNorm_one_eq_lintegral_enorm, finiteness, h_eq, lintegral_eq_lintegral, map_apply, map_lintegral, measureReal_def, measure_preimage_lt_top_of_integrable, mul_comm, norm_nonneg
-/
theorem norm_eq_sum_mul (f : α ->₁ₛ[μ] G) :
    ‖f‖ = ∑ x in (toSimpleFunc f).range, μ.real (toSimpleFunc f ⁻¹' {x}) * ‖x‖ := by
  rw [norm_toSimpleFunc]; rw [eLpNorm_one_eq_lintegral_enorm]
  have h_eq := SimpleFunc.map_apply (‖·‖ₑ) (toSimpleFunc f)
  simp_rw [← h_eq, measureReal_def]
  rw [SimpleFunc.lintegral_eq_lintegral]; rw [SimpleFunc.map_lintegral]; rw [ENNReal.toReal_sum]
  · congr
    ext1 x
    rw [ENNReal.toReal_mul]; rw [mul_comm]; rw [← ofReal_norm]; rw [ENNReal.toReal_ofReal (norm_nonneg _)]
  · intro x _
    by_cases hx0 : x = 0
    · rw [hx0]; simp
    · finiteness [SimpleFunc.measure_preimage_lt_top_of_integrable _ (SimpleFunc.integrable f) hx0]

section SetToL1S

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

attribute [local instance] Lp.simpleFunc.module

attribute [local instance] Lp.simpleFunc.normedSpace

/--
Definition of `setToL1S` / `setToL1S` 的定义

English:
definition setToL1S
  signature: (T : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E)
  body: (toSimpleFunc f).setToSimpleFunc T

中文:
定义 setToL1S
  签名: (T : 集合 α -> E ->L[实数] F) (f : α ->₁ₛ[μ] E)
  定义体: (toSimpleFunc f).setToSimpleFunc T

Depends on / 依赖: setToSimpleFunc, toSimpleFunc
-/
def setToL1S (T : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E) : F :=
  (toSimpleFunc f).setToSimpleFunc T

/--
theorem `setToL1S_eq_setToSimpleFunc` / 定理 `setToL1S_eq_setToSimpleFunc`

English:
theorem setToL1S_eq_setToSimpleFunc
  given: (T : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E)
  proof: rfl

@[simp]

中文:
定理 setToL1S_eq_setToSimpleFunc
  条件: (T : 集合 α -> E ->L[实数] F) (f : α ->₁ₛ[μ] E)
  证明: rfl

@[simp]
-/
theorem setToL1S_eq_setToSimpleFunc (T : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E) :
    setToL1S T f = (toSimpleFunc f).setToSimpleFunc T :=
  rfl

@[simp]
/--
theorem `setToL1S_zero_left` / 定理 `setToL1S_zero_left`

English:
theorem setToL1S_zero_left
  given: (f : α ->₁ₛ[μ] E)
  statement: setToL1S (0 : Set α -> E ->L[Real] F) f = 0
  proof: SimpleFunc.setToSimpleFunc_zero _

中文:
定理 setToL1S_zero_left
  条件: (f : α ->₁ₛ[μ] E)
  结论: setToL1S (0 : 集合 α -> E ->L[实数] F) f = 0
  证明: SimpleFunc.setToSimpleFunc_zero _

Depends on / 依赖: SimpleFunc, SimpleFunc.setToSimpleFunc_zero, setToSimpleFunc_zero
-/
theorem setToL1S_zero_left (f : α ->₁ₛ[μ] E) : setToL1S (0 : Set α -> E ->L[Real] F) f = 0 :=
  SimpleFunc.setToSimpleFunc_zero _

/--
theorem `setToL1S_zero_left'` / 定理 `setToL1S_zero_left'`

English:
theorem setToL1S_zero_left'
  statement: {T : Set α -> E ->L[Real] F}
  proof: SimpleFunc.setToSimpleFunc_zero' h_zero _ (SimpleFunc.integrable f)

中文:
定理 setToL1S_zero_left'
  结论: {T : 集合 α -> E ->L[实数] F}
  证明: SimpleFunc.setToSimpleFunc_zero' h_zero _ (SimpleFunc.integrable f)

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_zero, h_zero, integrable, setToSimpleFunc_zero
-/
theorem setToL1S_zero_left' {T : Set α -> E ->L[Real] F}
    (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0) (f : α ->₁ₛ[μ] E) : setToL1S T f = 0 :=
  SimpleFunc.setToSimpleFunc_zero' h_zero _ (SimpleFunc.integrable f)

/--
theorem `setToL1S_congr` / 定理 `setToL1S_congr`

English:
theorem setToL1S_congr
  statement: (T : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
  proof: SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) h

中文:
定理 setToL1S_congr
  结论: (T : 集合 α -> E ->L[实数] F) (h_zero : 对任意 s, 可测集 s -> μ s = 0 -> T s = 0)
  证明: SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) h

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_congr, h_add, h_zero, integrable, setToSimpleFunc_congr
-/
theorem setToL1S_congr (T : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
    (h_add : FinMeasAdditive μ T) {f g : α ->₁ₛ[μ] E} (h : toSimpleFunc f =ᵐ[μ] toSimpleFunc g) :
    setToL1S T f = setToL1S T g :=
  SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) h

/--
theorem `setToL1S_congr_left` / 定理 `setToL1S_congr_left`

English:
theorem setToL1S_congr_left
  statement: (T T' : Set α -> E ->L[Real] F)
  proof: SimpleFunc.setToSimpleFunc_congr_left T T' h (simpleFunc.toSimpleFunc f) (SimpleFunc.integrable f)

中文:
定理 setToL1S_congr_left
  结论: (T T' : 集合 α -> E ->L[实数] F)
  证明: SimpleFunc.setToSimpleFunc_congr_left T T' h (simpleFunc.toSimpleFunc f) (SimpleFunc.integrable f)

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_congr_left, integrable, setToSimpleFunc_congr_left, simpleFunc, simpleFunc.toSimpleFunc, toSimpleFunc
-/
theorem setToL1S_congr_left (T T' : Set α -> E ->L[Real] F)
    (h : forall s, MeasurableSet s -> μ s < ∞ -> T s = T' s) (f : α ->₁ₛ[μ] E) :
    setToL1S T f = setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_congr_left T T' h (simpleFunc.toSimpleFunc f) (SimpleFunc.integrable f)

/--
theorem `setToL1S_congr_measure` / 定理 `setToL1S_congr_measure`

English:
theorem setToL1S_congr_measure
  statement: {μ' : Measure α} (T : Set α -> E ->L[Real] F)
  proof: by
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) ?_
  refine (toSimpleFunc_eq_toFun f).trans ?_
  suffices (f' : α -> E) =ᵐ[μ] simpleFunc.toSimpleFunc f' from h.trans this
  have goal' : (f' : α -> E) =ᵐ[μ'] simpleFunc.toSimpleFunc f' := (toSimpleFunc_eq_toFun f'

中文:
定理 setToL1S_congr_measure
  结论: {μ' : 测度 α} (T : 集合 α -> E ->L[实数] F)
  证明: by
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) ?_
  refine (toSimpleFunc_eq_toFun f).trans ?_
  suffices (f' : α -> E) =ᵐ[μ] simpleFunc.toSimpleFunc f' from h.trans this
  have goal' : (f' : α -> E) =ᵐ[μ'] simpleFunc.toSimpleFunc f' := (toSimpleFunc_eq_toFun f'

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_congr, ae_eq, h.trans, h_add, h_zero, integrable, setToSimpleFunc_congr, simpleFunc, simpleFunc.toSimpleFunc, toSimpleFunc, toSimpleFunc_eq_toFun
-/
theorem setToL1S_congr_measure {μ' : Measure α} (T : Set α -> E ->L[Real] F)
    (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (hμ : μ ≪ μ')
    (f : α ->₁ₛ[μ] E) (f' : α ->₁ₛ[μ'] E) (h : (f : α -> E) =ᵐ[μ] f') :
    setToL1S T f = setToL1S T f' := by
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) ?_
  refine (toSimpleFunc_eq_toFun f).trans ?_
  suffices (f' : α -> E) =ᵐ[μ] simpleFunc.toSimpleFunc f' from h.trans this
  have goal' : (f' : α -> E) =ᵐ[μ'] simpleFunc.toSimpleFunc f' := (toSimpleFunc_eq_toFun f').symm
  exact hμ.ae_eq goal'

/--
theorem `setToL1S_add_left` / 定理 `setToL1S_add_left`

English:
theorem setToL1S_add_left
  given: (T T' : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E)
  proof: SimpleFunc.setToSimpleFunc_add_left T T'

中文:
定理 setToL1S_add_left
  条件: (T T' : 集合 α -> E ->L[实数] F) (f : α ->₁ₛ[μ] E)
  证明: SimpleFunc.setToSimpleFunc_add_left T T'

Depends on / 依赖: SimpleFunc, SimpleFunc.setToSimpleFunc_add_left, setToSimpleFunc_add_left
-/
theorem setToL1S_add_left (T T' : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E) :
    setToL1S (T + T') f = setToL1S T f + setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_add_left T T'

/--
theorem `setToL1S_add_left'` / 定理 `setToL1S_add_left'`

English:
theorem setToL1S_add_left'
  statement: (T T' T'' : Set α -> E ->L[Real] F)
  proof: SimpleFunc.setToSimpleFunc_add_left' T T' T'' h_add (SimpleFunc.integrable f)

中文:
定理 setToL1S_add_left'
  结论: (T T' T'' : 集合 α -> E ->L[实数] F)
  证明: SimpleFunc.setToSimpleFunc_add_left' T T' T'' h_add (SimpleFunc.integrable f)

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_add_left, h_add, integrable, setToSimpleFunc_add_left
-/
theorem setToL1S_add_left' (T T' T'' : Set α -> E ->L[Real] F)
    (h_add : forall s, MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) (f : α ->₁ₛ[μ] E) :
    setToL1S T'' f = setToL1S T f + setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_add_left' T T' T'' h_add (SimpleFunc.integrable f)

/--
theorem `setToL1S_smul_left` / 定理 `setToL1S_smul_left`

English:
theorem setToL1S_smul_left
  given: (T : Set α -> E ->L[Real] F) (c : Real) (f : α ->₁ₛ[μ] E)
  proof: SimpleFunc.setToSimpleFunc_smul_left T c _

中文:
定理 setToL1S_smul_left
  条件: (T : 集合 α -> E ->L[实数] F) (c : 实数) (f : α ->₁ₛ[μ] E)
  证明: SimpleFunc.setToSimpleFunc_smul_left T c _

Depends on / 依赖: SimpleFunc, SimpleFunc.setToSimpleFunc_smul_left, setToSimpleFunc_smul_left
-/
theorem setToL1S_smul_left (T : Set α -> E ->L[Real] F) (c : Real) (f : α ->₁ₛ[μ] E) :
    setToL1S (fun s => c • T s) f = c • setToL1S T f :=
  SimpleFunc.setToSimpleFunc_smul_left T c _

/--
theorem `setToL1S_smul_left'` / 定理 `setToL1S_smul_left'`

English:
theorem setToL1S_smul_left'
  statement: (T T' : Set α -> E ->L[Real] F) (c : Real)
  proof: SimpleFunc.setToSimpleFunc_smul_left' T T' c h_smul (SimpleFunc.integrable f)

中文:
定理 setToL1S_smul_left'
  结论: (T T' : 集合 α -> E ->L[实数] F) (c : 实数)
  证明: SimpleFunc.setToSimpleFunc_smul_left' T T' c h_smul (SimpleFunc.integrable f)

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_smul_left, h_smul, integrable, setToSimpleFunc_smul_left
-/
theorem setToL1S_smul_left' (T T' : Set α -> E ->L[Real] F) (c : Real)
    (h_smul : forall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s) (f : α ->₁ₛ[μ] E) :
    setToL1S T' f = c • setToL1S T f :=
  SimpleFunc.setToSimpleFunc_smul_left' T T' c h_smul (SimpleFunc.integrable f)

/--
theorem `setToL1S_add` / 定理 `setToL1S_add`

English:
theorem setToL1S_add
  statement: (T : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
  proof: by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_add T h_add (SimpleFunc.integrable f)
      (SimpleFunc.integrable g)]
  exact
    SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _)
      (add_toSimpleFunc f g)

中文:
定理 setToL1S_add
  结论: (T : 集合 α -> E ->L[实数] F) (h_zero : 对任意 s, 可测集 s -> μ s = 0 -> T s = 0)
  证明: by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_add T h_add (SimpleFunc.integrable f)
      (SimpleFunc.integrable g)]
  exact
    SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _)
      (add_toSimpleFunc f g)

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_add, SimpleFunc.setToSimpleFunc_congr, add_toSimpleFunc, h_add, h_zero, integrable, setToL1S, setToSimpleFunc_add, setToSimpleFunc_congr, simp_rw
-/
theorem setToL1S_add (T : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
    (h_add : FinMeasAdditive μ T) (f g : α ->₁ₛ[μ] E) :
    setToL1S T (f + g) = setToL1S T f + setToL1S T g := by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_add T h_add (SimpleFunc.integrable f)
      (SimpleFunc.integrable g)]
  exact
    SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _)
      (add_toSimpleFunc f g)

/--
theorem `setToL1S_neg` / 定理 `setToL1S_neg`

English:
theorem setToL1S_neg
  statement: {T : Set α -> E ->L[Real] F} (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
  proof: by
  simp_rw [setToL1S]
  have : simpleFunc.toSimpleFunc (-f) =ᵐ[μ] ⇑(-simpleFunc.toSimpleFunc f) :=
    neg_toSimpleFunc f
  rw [SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) this]
  exact SimpleFunc.setToSimpleFunc_neg T h_add (SimpleFunc.integrable f)

中文:
定理 setToL1S_neg
  结论: {T : 集合 α -> E ->L[实数] F} (h_zero : 对任意 s, 可测集 s -> μ s = 0 -> T s = 0)
  证明: by
  simp_rw [setToL1S]
  have : simpleFunc.toSimpleFunc (-f) =ᵐ[μ] ⇑(-simpleFunc.toSimpleFunc f) :=
    neg_toSimpleFunc f
  rw [SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) this]
  exact SimpleFunc.setToSimpleFunc_neg T h_add (SimpleFunc.integrable f)

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_congr, SimpleFunc.setToSimpleFunc_neg, h_add, h_zero, integrable, neg_toSimpleFunc, setToL1S, setToSimpleFunc_congr, setToSimpleFunc_neg, simp_rw, simpleFunc, simpleFunc.toSimpleFunc, toSimpleFunc
-/
theorem setToL1S_neg {T : Set α -> E ->L[Real] F} (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
    (h_add : FinMeasAdditive μ T) (f : α ->₁ₛ[μ] E) : setToL1S T (-f) = -setToL1S T f := by
  simp_rw [setToL1S]
  have : simpleFunc.toSimpleFunc (-f) =ᵐ[μ] ⇑(-simpleFunc.toSimpleFunc f) :=
    neg_toSimpleFunc f
  rw [SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) this]
  exact SimpleFunc.setToSimpleFunc_neg T h_add (SimpleFunc.integrable f)

/--
theorem `setToL1S_sub` / 定理 `setToL1S_sub`

English:
theorem setToL1S_sub
  statement: {T : Set α -> E ->L[Real] F} (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
  proof: by
  rw [sub_eq_add_neg]; rw [setToL1S_add T h_zero h_add]; rw [setToL1S_neg h_zero h_add]; rw [sub_eq_add_neg]

中文:
定理 setToL1S_sub
  结论: {T : 集合 α -> E ->L[实数] F} (h_zero : 对任意 s, 可测集 s -> μ s = 0 -> T s = 0)
  证明: by
  rw [sub_eq_add_neg]; rw [setToL1S_add T h_zero h_add]; rw [setToL1S_neg h_zero h_add]; rw [sub_eq_add_neg]

Depends on / 依赖: h_add, h_zero, setToL1S_add, setToL1S_neg, sub_eq_add_neg
-/
theorem setToL1S_sub {T : Set α -> E ->L[Real] F} (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
    (h_add : FinMeasAdditive μ T) (f g : α ->₁ₛ[μ] E) :
    setToL1S T (f - g) = setToL1S T f - setToL1S T g := by
  rw [sub_eq_add_neg]; rw [setToL1S_add T h_zero h_add]; rw [setToL1S_neg h_zero h_add]; rw [sub_eq_add_neg]

/--
theorem `setToL1S_smul_real` / 定理 `setToL1S_smul_real`

English:
theorem setToL1S_smul_real
  statement: (T : Set α -> E ->L[Real] F)
  proof: by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_smul_real T h_add c (SimpleFunc.integrable f)]
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact smul_toSimpleFunc c f

中文:
定理 setToL1S_smul_real
  结论: (T : 集合 α -> E ->L[实数] F)
  证明: by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_smul_real T h_add c (SimpleFunc.integrable f)]
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact smul_toSimpleFunc c f

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_congr, SimpleFunc.setToSimpleFunc_smul_real, h_add, h_zero, integrable, setToL1S, setToSimpleFunc_congr, setToSimpleFunc_smul_real, simp_rw, smul_toSimpleFunc
-/
theorem setToL1S_smul_real (T : Set α -> E ->L[Real] F)
    (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (c : Real)
    (f : α ->₁ₛ[μ] E) : setToL1S T (c • f) = c • setToL1S T f := by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_smul_real T h_add c (SimpleFunc.integrable f)]
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact smul_toSimpleFunc c f

/--
theorem `setToL1S_smul` / 定理 `setToL1S_smul`

English:
theorem setToL1S_smul
  proof: by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_smul T h_add h_smul c (SimpleFunc.integrable f)]
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact smul_toSimpleFunc c f

中文:
定理 setToL1S_smul
  证明: by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_smul T h_add h_smul c (SimpleFunc.integrable f)]
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact smul_toSimpleFunc c f

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_congr, SimpleFunc.setToSimpleFunc_smul, h_add, h_smul, h_zero, integrable, setToL1S, setToSimpleFunc_congr, setToSimpleFunc_smul, simp_rw, smul_toSimpleFunc
-/
theorem setToL1S_smul
    [DistribSMul 𝕜 F] (T : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
    (h_add : FinMeasAdditive μ T) (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (c : 𝕜)
    (f : α ->₁ₛ[μ] E) : setToL1S T (c • f) = c • setToL1S T f := by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_smul T h_add h_smul c (SimpleFunc.integrable f)]
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact smul_toSimpleFunc c f

/--
theorem `norm_setToL1S_le` / 定理 `norm_setToL1S_le`

English:
theorem norm_setToL1S_le
  statement: (T : Set α -> E ->L[Real] F) {C : Real}
  proof: by
  rw [setToL1S]; rw [norm_eq_sum_mul f]
  exact
    SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integrable T hT_norm _
      (SimpleFunc.integrable f)

中文:
定理 norm_setToL1S_le
  结论: (T : 集合 α -> E ->L[实数] F) {C : 实数}
  证明: by
  rw [setToL1S]; rw [norm_eq_sum_mul f]
  exact
    SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integrable T hT_norm _
      (SimpleFunc.integrable f)

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integrable, hT_norm, integrable, norm_eq_sum_mul, norm_setToSimpleFunc_le_sum_mul_norm_of_integrable, setToL1S
-/
theorem norm_setToL1S_le (T : Set α -> E ->L[Real] F) {C : Real}
    (hT_norm : forall s, MeasurableSet s -> μ s < ∞ -> ‖T s‖ <= C * μ.real s) (f : α ->₁ₛ[μ] E) :
    ‖setToL1S T f‖ <= C * ‖f‖ := by
  rw [setToL1S]; rw [norm_eq_sum_mul f]
  exact
    SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integrable T hT_norm _
      (SimpleFunc.integrable f)

/--
theorem `setToL1S_indicatorConst` / 定理 `setToL1S_indicatorConst`

English:
theorem setToL1S_indicatorConst
  statement: {T : Set α -> E ->L[Real] F} {s : Set α}
  proof: by
  have h_empty : T ∅ = 0 := h_zero _ MeasurableSet.empty measure_empty
  rw [setToL1S_eq_setToSimpleFunc]
  refine Eq.trans ?_ (SimpleFunc.setToSimpleFunc_indicator T h_empty hs x)
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact toSimpleFunc_indicator

中文:
定理 setToL1S_indicatorConst
  结论: {T : 集合 α -> E ->L[实数] F} {s : 集合 α}
  证明: by
  have h_empty : T ∅ = 0 := h_zero _ MeasurableSet.empty measure_empty
  rw [setToL1S_eq_setToSimpleFunc]
  refine Eq.trans ?_ (SimpleFunc.setToSimpleFunc_indicator T h_empty hs x)
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact toSimpleFunc_indicator

Depends on / 依赖: Eq.trans, MeasurableSet, MeasurableSet.empty, SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_congr, SimpleFunc.setToSimpleFunc_indicator, h_add, h_empty, h_zero, integrable, measure_empty, s.ne, setToL1S_eq_setToSimpleFunc, setToSimpleFunc_congr, setToSimpleFunc_indicator, toSimpleFunc_indicatorConst
-/
theorem setToL1S_indicatorConst {T : Set α -> E ->L[Real] F} {s : Set α}
    (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T)
    (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) :
    setToL1S T (simpleFunc.indicatorConst 1 hs hμs.ne x) = T s x := by
  have h_empty : T ∅ = 0 := h_zero _ MeasurableSet.empty measure_empty
  rw [setToL1S_eq_setToSimpleFunc]
  refine Eq.trans ?_ (SimpleFunc.setToSimpleFunc_indicator T h_empty hs x)
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact toSimpleFunc_indicatorConst hs hμs.ne x

/--
theorem `setToL1S_const` / 定理 `setToL1S_const`

English:
theorem setToL1S_const
  statement: [IsFiniteMeasure μ] {T : Set α -> E ->L[Real] F}
  proof: setToL1S_indicatorConst h_zero h_add MeasurableSet.univ (measure_lt_top _ _) x

中文:
定理 setToL1S_const
  结论: [是有限测度 μ] {T : 集合 α -> E ->L[实数] F}
  证明: setToL1S_indicatorConst h_zero h_add MeasurableSet.univ (measure_lt_top _ _) x

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, h_add, h_zero, measure_lt_top, setToL1S_indicatorConst
-/
theorem setToL1S_const [IsFiniteMeasure μ] {T : Set α -> E ->L[Real] F}
    (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (x : E) :
    setToL1S T (simpleFunc.indicatorConst 1 MeasurableSet.univ (measure_ne_top μ _) x) = T univ x :=
  setToL1S_indicatorConst h_zero h_add MeasurableSet.univ (measure_lt_top _ _) x

section Order

variable {G'' G' : Type*}
  [NormedAddCommGroup G'] [PartialOrder G'] [IsOrderedAddMonoid G'] [NormedSpace Real G']
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G''] [NormedSpace Real G'']
  {T : Set α -> G'' ->L[Real] G'}

/--
theorem `setToL1S_mono_left` / 定理 `setToL1S_mono_left`

English:
theorem setToL1S_mono_left
  statement: {T T' : Set α -> E ->L[Real] G''} (hTT' : forall s x, T s x <= T' s x)
  proof: SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _

中文:
定理 setToL1S_mono_left
  结论: {T T' : 集合 α -> E ->L[实数] G''} (hTT' : 对任意 s x, T s x <= T' s x)
  证明: SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _

Depends on / 依赖: SimpleFunc, SimpleFunc.setToSimpleFunc_mono_left, setToSimpleFunc_mono_left
-/
theorem setToL1S_mono_left {T T' : Set α -> E ->L[Real] G''} (hTT' : forall s x, T s x <= T' s x)
    (f : α ->₁ₛ[μ] E) : setToL1S T f <= setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _

/--
theorem `setToL1S_mono_left'` / 定理 `setToL1S_mono_left'`

English:
theorem setToL1S_mono_left'
  statement: {T T' : Set α -> E ->L[Real] G''}
  proof: SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)

omit [IsOrderedAddMonoid G''] in

中文:
定理 setToL1S_mono_left'
  结论: {T T' : 集合 α -> E ->L[实数] G''}
  证明: SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)

omit [IsOrderedAddMonoid G''] in

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_mono_left, integrable, setToSimpleFunc_mono_left
-/
theorem setToL1S_mono_left' {T T' : Set α -> E ->L[Real] G''}
    (hTT' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x) (f : α ->₁ₛ[μ] E) :
    setToL1S T f <= setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)

omit [IsOrderedAddMonoid G''] in
/--
theorem `setToL1S_nonneg` / 定理 `setToL1S_nonneg`

English:
theorem setToL1S_nonneg
  statement: (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
  proof: by
  simp_rw [setToL1S]
  obtain ⟨f', hf', hff'⟩ := exists_simpleFunc_nonneg_ae_eq hf
  replace hff' : simpleFunc.toSimpleFunc f =ᵐ[μ] f' :=
    (Lp.simpleFunc.toSimpleFunc_eq_toFun f).trans hff'
  rw [SimpleFunc.setToSimpleFunc_congr _ h_zero h_add (SimpleFunc.integrable _) hff']
  exact
    Simple

中文:
定理 setToL1S_nonneg
  结论: (h_zero : 对任意 s, 可测集 s -> μ s = 0 -> T s = 0)
  证明: by
  simp_rw [setToL1S]
  obtain ⟨f', hf', hff'⟩ := exists_simpleFunc_nonneg_ae_eq hf
  replace hff' : simpleFunc.toSimpleFunc f =ᵐ[μ] f' :=
    (Lp.simpleFunc.toSimpleFunc_eq_toFun f).trans hff'
  rw [SimpleFunc.setToSimpleFunc_congr _ h_zero h_add (SimpleFunc.integrable _) hff']
  exact
    Simple

Depends on / 依赖: Lp.simpleFunc.toSimpleFunc_eq_toFun, SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_congr, SimpleFunc.setToSimpleFunc_nonneg, exists_simpleFunc_nonneg_ae_eq, hT_nonneg, h_add, h_zero, integrable, replace, setToL1S, setToSimpleFunc_congr, setToSimpleFunc_nonneg, simp_rw, simpleFunc, simpleFunc.toSimpleFunc, toSimpleFunc, toSimpleFunc_eq_toFun
-/
theorem setToL1S_nonneg (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
    (h_add : FinMeasAdditive μ T)
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f : α ->₁ₛ[μ] G''}
    (hf : 0 <= f) : 0 <= setToL1S T f := by
  simp_rw [setToL1S]
  obtain ⟨f', hf', hff'⟩ := exists_simpleFunc_nonneg_ae_eq hf
  replace hff' : simpleFunc.toSimpleFunc f =ᵐ[μ] f' :=
    (Lp.simpleFunc.toSimpleFunc_eq_toFun f).trans hff'
  rw [SimpleFunc.setToSimpleFunc_congr _ h_zero h_add (SimpleFunc.integrable _) hff']
  exact
    SimpleFunc.setToSimpleFunc_nonneg' T hT_nonneg _ hf' ((SimpleFunc.integrable f).congr hff')

/--
theorem `setToL1S_mono` / 定理 `setToL1S_mono`

English:
theorem setToL1S_mono
  statement: (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
  proof: by
  rw [← sub_nonneg] at hfg ⊢
  rw [← setToL1S_sub h_zero h_add]
  exact setToL1S_nonneg h_zero h_add hT_nonneg hfg

中文:
定理 setToL1S_mono
  结论: (h_zero : 对任意 s, 可测集 s -> μ s = 0 -> T s = 0)
  证明: by
  rw [← sub_nonneg] at hfg ⊢
  rw [← setToL1S_sub h_zero h_add]
  exact setToL1S_nonneg h_zero h_add hT_nonneg hfg

Depends on / 依赖: hT_nonneg, h_add, h_zero, setToL1S_nonneg, setToL1S_sub, sub_nonneg
-/
theorem setToL1S_mono (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
    (h_add : FinMeasAdditive μ T)
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f g : α ->₁ₛ[μ] G''}
    (hfg : f <= g) : setToL1S T f <= setToL1S T g := by
  rw [← sub_nonneg] at hfg ⊢
  rw [← setToL1S_sub h_zero h_add]
  exact setToL1S_nonneg h_zero h_add hT_nonneg hfg

end Order

variable [Module 𝕜 F] [IsBoundedSMul 𝕜 F]
variable (α E μ 𝕜)

/--
Definition of `setToL1SCLM'` / `setToL1SCLM'` 的定义

English:
definition setToL1SCLM'
  signature: {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
  body: LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul T (fun _ => hT.eq_zero_of_measure_zero) hT.1 h_smul⟩
    C fun f => norm_setToL1S_le T hT.2 f

中文:
定义 setToL1SCLM'
  签名: {T : 集合 α -> E ->L[实数] F} {C : 实数} (hT : DominatedFinMeasAdditive μ T C)
  定义体: LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul T (fun _ => hT.eq_zero_of_measure_zero) hT.1 h_smul⟩
    C fun f => norm_setToL1S_le T hT.2 f

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, eq_zero_of_measure_zero, hT.eq_zero_of_measure_zero, h_smul, mkContinuous, norm_setToL1S_le, setToL1S, setToL1S_add, setToL1S_smul
-/
def setToL1SCLM' {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) : (α ->₁ₛ[μ] E) ->L[𝕜] F :=
  LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul T (fun _ => hT.eq_zero_of_measure_zero) hT.1 h_smul⟩
    C fun f => norm_setToL1S_le T hT.2 f

/--
Definition of `setToL1SCLM` / `setToL1SCLM` 的定义

English:
definition setToL1SCLM
  signature: {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
  body: LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul_real T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩
    C fun f => norm_setToL1S_le T hT.2 f

中文:
定义 setToL1SCLM
  签名: {T : 集合 α -> E ->L[实数] F} {C : 实数} (hT : DominatedFinMeasAdditive μ T C)
  定义体: LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul_real T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩
    C fun f => norm_setToL1S_le T hT.2 f

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, eq_zero_of_measure_zero, hT.eq_zero_of_measure_zero, mkContinuous, norm_setToL1S_le, setToL1S, setToL1S_add, setToL1S_smul_real
-/
def setToL1SCLM {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C) :
    (α ->₁ₛ[μ] E) ->L[Real] F :=
  LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul_real T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩
    C fun f => norm_setToL1S_le T hT.2 f

variable {α E μ 𝕜}
variable {T T' T'' : Set α -> E ->L[Real] F} {C C' C'' : Real}

@[simp]
/--
theorem `setToL1SCLM_zero_left` / 定理 `setToL1SCLM_zero_left`

English:
theorem setToL1SCLM_zero_left
  statement: (hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Real] F) C)
  proof: setToL1S_zero_left _

中文:
定理 setToL1SCLM_zero_left
  结论: (hT : DominatedFinMeasAdditive μ (0 : 集合 α -> E ->L[实数] F) C)
  证明: setToL1S_zero_left _

Depends on / 依赖: setToL1S_zero_left
-/
theorem setToL1SCLM_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Real] F) C)
    (f : α ->₁ₛ[μ] E) : setToL1SCLM α E μ hT f = 0 :=
  setToL1S_zero_left _

/--
theorem `setToL1SCLM_zero_left'` / 定理 `setToL1SCLM_zero_left'`

English:
theorem setToL1SCLM_zero_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1S_zero_left' h_zero f

中文:
定理 setToL1SCLM_zero_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1S_zero_left' h_zero f

Depends on / 依赖: h_zero, setToL1S_zero_left
-/
theorem setToL1SCLM_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0) (f : α ->₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f = 0 :=
  setToL1S_zero_left' h_zero f

/--
theorem `setToL1SCLM_congr_left` / 定理 `setToL1SCLM_congr_left`

English:
theorem setToL1SCLM_congr_left
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1S_congr_left T T' (fun _ _ _ => by rw [h]) f

中文:
定理 setToL1SCLM_congr_left
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1S_congr_left T T' (fun _ _ _ => by rw [h]) f

Depends on / 依赖: setToL1S_congr_left
-/
theorem setToL1SCLM_congr_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T') (f : α ->₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f = setToL1SCLM α E μ hT' f :=
  setToL1S_congr_left T T' (fun _ _ _ => by rw [h]) f

/--
theorem `setToL1SCLM_congr_left'` / 定理 `setToL1SCLM_congr_left'`

English:
theorem setToL1SCLM_congr_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1S_congr_left T T' h f

中文:
定理 setToL1SCLM_congr_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1S_congr_left T T' h f

Depends on / 依赖: setToL1S_congr_left
-/
theorem setToL1SCLM_congr_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : forall s, MeasurableSet s -> μ s < ∞ -> T s = T' s)
    (f : α ->₁ₛ[μ] E) : setToL1SCLM α E μ hT f = setToL1SCLM α E μ hT' f :=
  setToL1S_congr_left T T' h f

/--
theorem `setToL1SCLM_congr_measure` / 定理 `setToL1SCLM_congr_measure`

English:
theorem setToL1SCLM_congr_measure
  statement: {μ' : Measure α} (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1S_congr_measure T (fun _ => hT.eq_zero_of_measure_zero) hT.1 hμ _ _ h

中文:
定理 setToL1SCLM_congr_measure
  结论: {μ' : 测度 α} (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1S_congr_measure T (fun _ => hT.eq_zero_of_measure_zero) hT.1 hμ _ _ h

Depends on / 依赖: eq_zero_of_measure_zero, hT.eq_zero_of_measure_zero, setToL1S_congr_measure
-/
theorem setToL1SCLM_congr_measure {μ' : Measure α} (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (hμ : μ ≪ μ') (f : α ->₁ₛ[μ] E) (f' : α ->₁ₛ[μ'] E)
    (h : (f : α -> E) =ᵐ[μ] f') : setToL1SCLM α E μ hT f = setToL1SCLM α E μ' hT' f' :=
  setToL1S_congr_measure T (fun _ => hT.eq_zero_of_measure_zero) hT.1 hμ _ _ h

/--
theorem `setToL1SCLM_add_left` / 定理 `setToL1SCLM_add_left`

English:
theorem setToL1SCLM_add_left
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1S_add_left T T' f

中文:
定理 setToL1SCLM_add_left
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1S_add_left T T' f

Depends on / 依赖: setToL1S_add_left
-/
theorem setToL1SCLM_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α ->₁ₛ[μ] E) :
    setToL1SCLM α E μ (hT.add hT') f = setToL1SCLM α E μ hT f + setToL1SCLM α E μ hT' f :=
  setToL1S_add_left T T' f

/--
theorem `setToL1SCLM_add_left'` / 定理 `setToL1SCLM_add_left'`

English:
theorem setToL1SCLM_add_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1S_add_left' T T' T'' h_add f

中文:
定理 setToL1SCLM_add_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1S_add_left' T T' T'' h_add f

Depends on / 依赖: h_add, setToL1S_add_left
-/
theorem setToL1SCLM_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : forall s, MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) (f : α ->₁ₛ[μ] E) :
    setToL1SCLM α E μ hT'' f = setToL1SCLM α E μ hT f + setToL1SCLM α E μ hT' f :=
  setToL1S_add_left' T T' T'' h_add f

/--
theorem `setToL1SCLM_smul_left` / 定理 `setToL1SCLM_smul_left`

English:
theorem setToL1SCLM_smul_left
  given: (c : Real) (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E)
  proof: setToL1S_smul_left T c f

中文:
定理 setToL1SCLM_smul_left
  条件: (c : 实数) (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E)
  证明: setToL1S_smul_left T c f

Depends on / 依赖: setToL1S_smul_left
-/
theorem setToL1SCLM_smul_left (c : Real) (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) :
    setToL1SCLM α E μ (hT.smul c) f = c • setToL1SCLM α E μ hT f :=
  setToL1S_smul_left T c f

/--
theorem `setToL1SCLM_smul_left'` / 定理 `setToL1SCLM_smul_left'`

English:
theorem setToL1SCLM_smul_left'
  statement: (c : Real) (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1S_smul_left' T T' c h_smul f

中文:
定理 setToL1SCLM_smul_left'
  结论: (c : 实数) (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1S_smul_left' T T' c h_smul f

Depends on / 依赖: h_smul, setToL1S_smul_left
-/
theorem setToL1SCLM_smul_left' (c : Real) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C')
    (h_smul : forall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s) (f : α ->₁ₛ[μ] E) :
    setToL1SCLM α E μ hT' f = c • setToL1SCLM α E μ hT f :=
  setToL1S_smul_left' T T' c h_smul f

/--
theorem `norm_setToL1SCLM_le` / 定理 `norm_setToL1SCLM_le`

English:
theorem norm_setToL1SCLM_le
  statement: {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
  proof: LinearMap.mkContinuous_norm_le _ hC _

中文:
定理 norm_setToL1SCLM_le
  结论: {T : 集合 α -> E ->L[实数] F} {C : 实数} (hT : DominatedFinMeasAdditive μ T C)
  证明: LinearMap.mkContinuous_norm_le _ hC _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, mkContinuous_norm_le
-/
theorem norm_setToL1SCLM_le {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 <= C) : ‖setToL1SCLM α E μ hT‖ <= C :=
  LinearMap.mkContinuous_norm_le _ hC _

/--
theorem `norm_setToL1SCLM_le'` / 定理 `norm_setToL1SCLM_le'`

English:
theorem norm_setToL1SCLM_le'
  given: {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
  proof: LinearMap.mkContinuous_norm_le' _ _

中文:
定理 norm_setToL1SCLM_le'
  条件: {T : 集合 α -> E ->L[实数] F} {C : 实数} (hT : DominatedFinMeasAdditive μ T C)
  证明: LinearMap.mkContinuous_norm_le' _ _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, mkContinuous_norm_le
-/
theorem norm_setToL1SCLM_le' {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C) :
    ‖setToL1SCLM α E μ hT‖ <= max C 0 :=
  LinearMap.mkContinuous_norm_le' _ _

/--
theorem `setToL1SCLM_const` / 定理 `setToL1SCLM_const`

English:
theorem setToL1SCLM_const
  statement: [IsFiniteMeasure μ] {T : Set α -> E ->L[Real] F} {C : Real}
  proof: setToL1S_const (fun _ => hT.eq_zero_of_measure_zero) hT.1 x

中文:
定理 setToL1SCLM_const
  结论: [是有限测度 μ] {T : 集合 α -> E ->L[实数] F} {C : 实数}
  证明: setToL1S_const (fun _ => hT.eq_zero_of_measure_zero) hT.1 x

Depends on / 依赖: eq_zero_of_measure_zero, hT.eq_zero_of_measure_zero, setToL1S_const
-/
theorem setToL1SCLM_const [IsFiniteMeasure μ] {T : Set α -> E ->L[Real] F} {C : Real}
    (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    setToL1SCLM α E μ hT (simpleFunc.indicatorConst 1 MeasurableSet.univ (measure_ne_top μ _) x) =
      T univ x :=
  setToL1S_const (fun _ => hT.eq_zero_of_measure_zero) hT.1 x

section Order

variable {G' G'' : Type*}
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G''] [NormedSpace Real G'']
  [NormedAddCommGroup G'] [PartialOrder G'] [IsOrderedAddMonoid G'] [NormedSpace Real G']

/--
theorem `setToL1SCLM_mono_left` / 定理 `setToL1SCLM_mono_left`

English:
theorem setToL1SCLM_mono_left
  statement: {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
  proof: SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _

中文:
定理 setToL1SCLM_mono_left
  结论: {T T' : 集合 α -> E ->L[实数] G''} {C C' : 实数}
  证明: SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _

Depends on / 依赖: SimpleFunc, SimpleFunc.setToSimpleFunc_mono_left, setToSimpleFunc_mono_left
-/
theorem setToL1SCLM_mono_left {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : forall s x, T s x <= T' s x) (f : α ->₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f <= setToL1SCLM α E μ hT' f :=
  SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _

/--
theorem `setToL1SCLM_mono_left'` / 定理 `setToL1SCLM_mono_left'`

English:
theorem setToL1SCLM_mono_left'
  statement: {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
  proof: SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)

omit [IsOrderedAddMonoid G'] in

中文:
定理 setToL1SCLM_mono_left'
  结论: {T T' : 集合 α -> E ->L[实数] G''} {C C' : 实数}
  证明: SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)

omit [IsOrderedAddMonoid G'] in

Depends on / 依赖: SimpleFunc, SimpleFunc.integrable, SimpleFunc.setToSimpleFunc_mono_left, integrable, setToSimpleFunc_mono_left
-/
theorem setToL1SCLM_mono_left' {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x) (f : α ->₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f <= setToL1SCLM α E μ hT' f :=
  SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)

omit [IsOrderedAddMonoid G'] in
/--
theorem `setToL1SCLM_nonneg` / 定理 `setToL1SCLM_nonneg`

English:
theorem setToL1SCLM_nonneg
  statement: {T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1S_nonneg (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hf

中文:
定理 setToL1SCLM_nonneg
  结论: {T : 集合 α -> G' ->L[实数] G''} {C : 实数} (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1S_nonneg (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hf

Depends on / 依赖: eq_zero_of_measure_zero, hT.eq_zero_of_measure_zero, hT_nonneg, setToL1S_nonneg
-/
theorem setToL1SCLM_nonneg {T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f : α ->₁ₛ[μ] G'}
    (hf : 0 <= f) : 0 <= setToL1SCLM α G' μ hT f :=
  setToL1S_nonneg (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hf

/--
theorem `setToL1SCLM_mono` / 定理 `setToL1SCLM_mono`

English:
theorem setToL1SCLM_mono
  statement: {T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1S_mono (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hfg

中文:
定理 setToL1SCLM_mono
  结论: {T : 集合 α -> G' ->L[实数] G''} {C : 实数} (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1S_mono (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hfg

Depends on / 依赖: eq_zero_of_measure_zero, hT.eq_zero_of_measure_zero, hT_nonneg, setToL1S_mono
-/
theorem setToL1SCLM_mono {T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f g : α ->₁ₛ[μ] G'}
    (hfg : f <= g) : setToL1SCLM α G' μ hT f <= setToL1SCLM α G' μ hT g :=
  setToL1S_mono (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hfg

end Order

end SetToL1S

end SimpleFunc

open L1.SimpleFunc

section SetToL1

attribute [local instance] Lp.simpleFunc.module

attribute [local instance] Lp.simpleFunc.normedSpace

variable (𝕜) [NormedRing 𝕜] [Module 𝕜 E] [Module 𝕜 F] [IsBoundedSMul 𝕜 E] [IsBoundedSMul 𝕜 F]
  [CompleteSpace F] {T T' T'' : Set α -> E ->L[Real] F} {C C' C'' : Real}

/--
Definition of `setToL1'` / `setToL1'` 的定义

English:
definition setToL1'
  signature: (hT : DominatedFinMeasAdditive μ T C)
  body: (setToL1SCLM' α E 𝕜 μ hT h_smul).extend (coeToLp α E 𝕜)

中文:
定义 setToL1'
  签名: (hT : DominatedFinMeasAdditive μ T C)
  定义体: (setToL1SCLM' α E 𝕜 μ hT h_smul).extend (coeToLp α E 𝕜)

Depends on / 依赖: coeToLp, extend, h_smul, setToL1SCLM
-/
def setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) : (α ->₁[μ] E) ->L[𝕜] F :=
  (setToL1SCLM' α E 𝕜 μ hT h_smul).extend (coeToLp α E 𝕜)

/--
theorem `setToL1'_eq_setToL1SCLM` / 定理 `setToL1'_eq_setToL1SCLM`

English:
theorem setToL1'_eq_setToL1SCLM
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  apply ContinuousLinearMap.extend_eq _ _ simpleFunc.isUniformInducing
  · exact simpleFunc.denseRange one_ne_top

@[simp]

中文:
定理 setToL1'_eq_setToL1SCLM
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  apply ContinuousLinearMap.extend_eq _ _ simpleFunc.isUniformInducing
  · exact simpleFunc.denseRange one_ne_top

@[simp]
-/
theorem setToL1'_eq_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (f : α ->₁ₛ[μ] E) :
    setToL1' 𝕜 hT h_smul f = setToL1SCLM α E μ hT f := by
  apply ContinuousLinearMap.extend_eq _ _ simpleFunc.isUniformInducing
  · exact simpleFunc.denseRange one_ne_top

@[simp]
/--
theorem `setToL1'_apply_coeToLp` / 定理 `setToL1'_apply_coeToLp`

English:
theorem setToL1'_apply_coeToLp
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1'_eq_setToL1SCLM 𝕜 hT h_smul f

中文:
定理 setToL1'_apply_coeToLp
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1'_eq_setToL1SCLM 𝕜 hT h_smul f
-/
theorem setToL1'_apply_coeToLp (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (f : α ->₁ₛ[μ] E) :
    setToL1' 𝕜 hT h_smul (coeToLp α E Real f) = setToL1SCLM α E μ hT f :=
  setToL1'_eq_setToL1SCLM 𝕜 hT h_smul f

variable {𝕜}

/--
Definition of `setToL1` / `setToL1` 的定义

English:
definition setToL1
  signature: (hT : DominatedFinMeasAdditive μ T C)
  body: (setToL1SCLM α E μ hT).extend (coeToLp α E Real)

中文:
定义 setToL1
  签名: (hT : DominatedFinMeasAdditive μ T C)
  定义体: (setToL1SCLM α E μ hT).extend (coeToLp α E Real)

Depends on / 依赖: coeToLp, extend, setToL1SCLM
-/
def setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α ->₁[μ] E) ->L[Real] F :=
  (setToL1SCLM α E μ hT).extend (coeToLp α E Real)

/--
theorem `setToL1_eq_setToL1SCLM` / 定理 `setToL1_eq_setToL1SCLM`

English:
theorem setToL1_eq_setToL1SCLM
  given: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E)
  proof: setToL1'_eq_setToL1SCLM Real hT (by simp) _

@[simp]

中文:
定理 setToL1_eq_setToL1SCLM
  条件: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E)
  证明: setToL1'_eq_setToL1SCLM Real hT (by simp) _

@[simp]

Depends on / 依赖: _eq_setToL1SCLM, setToL1
-/
theorem setToL1_eq_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) :
    setToL1 hT f = setToL1SCLM α E μ hT f :=
  setToL1'_eq_setToL1SCLM Real hT (by simp) _

@[simp]
/--
theorem `setToL1_apply_coeToLp` / 定理 `setToL1_apply_coeToLp`

English:
theorem setToL1_apply_coeToLp
  given: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E)
  proof: setToL1_eq_setToL1SCLM hT f

中文:
定理 setToL1_apply_coeToLp
  条件: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E)
  证明: setToL1_eq_setToL1SCLM hT f

Depends on / 依赖: setToL1_eq_setToL1SCLM
-/
theorem setToL1_apply_coeToLp (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) :
    setToL1 hT (coeToLp α E Real f) = setToL1SCLM α E μ hT f :=
  setToL1_eq_setToL1SCLM hT f

/--
theorem `setToL1_unique` / 定理 `setToL1_unique`

English:
theorem setToL1_unique
  statement: (hT : DominatedFinMeasAdditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F}
  proof: by
  suffices setToL1 hT = A by rw [this]
  apply ContinuousLinearMap.extend_unique
  · exact (simpleFunc.denseRange one_ne_top)
  · exact simpleFunc.isUniformInducing
  ext f
  rw [hA f]
  rfl

中文:
定理 setToL1_unique
  结论: (hT : DominatedFinMeasAdditive μ T C) {A : (α ->₁[μ] E) ->L[实数] F}
  证明: by
  suffices setToL1 hT = A by rw [this]
  apply ContinuousLinearMap.extend_unique
  · exact (simpleFunc.denseRange one_ne_top)
  · exact simpleFunc.isUniformInducing
  ext f
  rw [hA f]
  rfl

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.extend_unique, denseRange, extend_unique, isUniformInducing, one_ne_top, setToL1, simpleFunc, simpleFunc.denseRange, simpleFunc.isUniformInducing
-/
theorem setToL1_unique (hT : DominatedFinMeasAdditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F}
    (hA : forall f : α ->₁ₛ[μ] E, setToL1SCLM α E μ hT f = A f) (f : α ->₁[μ] E) :
    setToL1 hT f = A f := by
  suffices setToL1 hT = A by rw [this]
  apply ContinuousLinearMap.extend_unique
  · exact (simpleFunc.denseRange one_ne_top)
  · exact simpleFunc.isUniformInducing
  ext f
  rw [hA f]
  rfl

/--
theorem `setToL1_eq_setToL1'` / 定理 `setToL1_eq_setToL1'`

English:
theorem setToL1_eq_setToL1'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  have h₁ : Dense (Set.range (coeToLp α E Real)) := simpleFunc.denseRange (μ := μ) one_ne_top
  apply Dense.induction (P := fun f : α ->₁[μ] E => (setToL1 hT) f = (setToL1' 𝕜 hT h_smul) f) h₁
  · intro f ⟨f', hf⟩
    simp [← hf]
  · exact isClosed_eq (setToL1 hT).continuous (setToL1' 𝕜 hT h_smul)

中文:
定理 setToL1_eq_setToL1'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  have h₁ : Dense (Set.range (coeToLp α E Real)) := simpleFunc.denseRange (μ := μ) one_ne_top
  apply Dense.induction (P := fun f : α ->₁[μ] E => (setToL1 hT) f = (setToL1' 𝕜 hT h_smul) f) h₁
  · intro f ⟨f', hf⟩
    simp [← hf]
  · exact isClosed_eq (setToL1 hT).continuous (setToL1' 𝕜 hT h_smul)

Depends on / 依赖: Dense.induction, Set.range, coeToLp, continuous, denseRange, h_smul, isClosed_eq, one_ne_top, setToL1, simpleFunc, simpleFunc.denseRange
-/
theorem setToL1_eq_setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (f : α ->₁[μ] E) :
    setToL1 hT f = setToL1' 𝕜 hT h_smul f := by
  have h₁ : Dense (Set.range (coeToLp α E Real)) := simpleFunc.denseRange (μ := μ) one_ne_top
  apply Dense.induction (P := fun f : α ->₁[μ] E => (setToL1 hT) f = (setToL1' 𝕜 hT h_smul) f) h₁
  · intro f ⟨f', hf⟩
    simp [← hf]
  · exact isClosed_eq (setToL1 hT).continuous (setToL1' 𝕜 hT h_smul).continuous

@[simp]
/--
theorem `setToL1_zero_left` / 定理 `setToL1_zero_left`

English:
theorem setToL1_zero_left
  statement: (hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Real] F) C)
  proof: setToL1_unique hT (A := 0) (by simp) f

中文:
定理 setToL1_zero_left
  结论: (hT : DominatedFinMeasAdditive μ (0 : 集合 α -> E ->L[实数] F) C)
  证明: setToL1_unique hT (A := 0) (by simp) f

Depends on / 依赖: setToL1_unique
-/
theorem setToL1_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Real] F) C)
    (f : α ->₁[μ] E) : setToL1 hT f = 0 :=
  setToL1_unique hT (A := 0) (by simp) f

/--
theorem `setToL1_zero_left'` / 定理 `setToL1_zero_left'`

English:
theorem setToL1_zero_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: setToL1_unique hT (A := 0) (by simp [setToL1SCLM_zero_left' hT h_zero]) f

中文:
定理 setToL1_zero_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: setToL1_unique hT (A := 0) (by simp [setToL1SCLM_zero_left' hT h_zero]) f

Depends on / 依赖: h_zero, setToL1SCLM_zero_left, setToL1_unique
-/
theorem setToL1_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0) (f : α ->₁[μ] E) : setToL1 hT f = 0 :=
  setToL1_unique hT (A := 0) (by simp [setToL1SCLM_zero_left' hT h_zero]) f

/--
theorem `setToL1_congr_left` / 定理 `setToL1_congr_left`

English:
theorem setToL1_congr_left
  statement: (T T' : Set α -> E ->L[Real] F) {C C' : Real}
  proof: by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1SCLM_congr_left hT' hT h.symm f

中文:
定理 setToL1_congr_left
  结论: (T T' : 集合 α -> E ->L[实数] F) {C C' : 实数}
  证明: by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1SCLM_congr_left hT' hT h.symm f

Depends on / 依赖: h.symm, setToL1, setToL1SCLM, setToL1SCLM_congr_left, setToL1_eq_setToL1SCLM, setToL1_unique
-/
theorem setToL1_congr_left (T T' : Set α -> E ->L[Real] F) {C C' : Real}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T')
    (f : α ->₁[μ] E) : setToL1 hT f = setToL1 hT' f := by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1SCLM_congr_left hT' hT h.symm f

/--
theorem `setToL1_congr_left'` / 定理 `setToL1_congr_left'`

English:
theorem setToL1_congr_left'
  statement: (T T' : Set α -> E ->L[Real] F) {C C' : Real}
  proof: by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact (setToL1SCLM_congr_left' hT hT' h f).symm

中文:
定理 setToL1_congr_left'
  结论: (T T' : 集合 α -> E ->L[实数] F) {C C' : 实数}
  证明: by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact (setToL1SCLM_congr_left' hT hT' h f).symm

Depends on / 依赖: setToL1, setToL1SCLM, setToL1SCLM_congr_left, setToL1_eq_setToL1SCLM, setToL1_unique
-/
theorem setToL1_congr_left' (T T' : Set α -> E ->L[Real] F) {C C' : Real}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (h : forall s, MeasurableSet s -> μ s < ∞ -> T s = T' s) (f : α ->₁[μ] E) :
    setToL1 hT f = setToL1 hT' f := by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact (setToL1SCLM_congr_left' hT hT' h f).symm

/--
theorem `setToL1_add_left` / 定理 `setToL1_add_left`

English:
theorem setToL1_add_left
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  apply setToL1_unique (hT.add hT') (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left hT hT']

中文:
定理 setToL1_add_left
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  apply setToL1_unique (hT.add hT') (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left hT hT']

Depends on / 依赖: hT.add, setToL1, setToL1SCLM_add_left, setToL1_eq_setToL1SCLM, setToL1_unique
-/
theorem setToL1_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α ->₁[μ] E) :
    setToL1 (hT.add hT') f = setToL1 hT f + setToL1 hT' f := by
  apply setToL1_unique (hT.add hT') (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left hT hT']

/--
theorem `setToL1_add_left'` / 定理 `setToL1_add_left'`

English:
theorem setToL1_add_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  apply setToL1_unique hT'' (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left' hT hT' hT'' h_add]

中文:
定理 setToL1_add_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  apply setToL1_unique hT'' (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left' hT hT' hT'' h_add]

Depends on / 依赖: h_add, setToL1, setToL1SCLM_add_left, setToL1_eq_setToL1SCLM, setToL1_unique
-/
theorem setToL1_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : forall s, MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) (f : α ->₁[μ] E) :
    setToL1 hT'' f = setToL1 hT f + setToL1 hT' f := by
  apply setToL1_unique hT'' (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left' hT hT' hT'' h_add]

/--
theorem `setToL1_smul_left` / 定理 `setToL1_smul_left`

English:
theorem setToL1_smul_left
  given: (hT : DominatedFinMeasAdditive μ T C) (c : Real) (f : α ->₁[μ] E)
  proof: by
  apply setToL1_unique (hT.smul c) (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left c hT]

中文:
定理 setToL1_smul_left
  条件: (hT : DominatedFinMeasAdditive μ T C) (c : 实数) (f : α ->₁[μ] E)
  证明: by
  apply setToL1_unique (hT.smul c) (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left c hT]

Depends on / 依赖: hT.smul, setToL1, setToL1SCLM_smul_left, setToL1_eq_setToL1SCLM, setToL1_unique
-/
theorem setToL1_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : Real) (f : α ->₁[μ] E) :
    setToL1 (hT.smul c) f = c • setToL1 hT f := by
  apply setToL1_unique (hT.smul c) (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left c hT]

/--
theorem `setToL1_smul_left'` / 定理 `setToL1_smul_left'`

English:
theorem setToL1_smul_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  apply setToL1_unique hT' (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left' c hT hT' h_smul]

中文:
定理 setToL1_smul_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  apply setToL1_unique hT' (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left' c hT hT' h_smul]

Depends on / 依赖: h_smul, setToL1, setToL1SCLM_smul_left, setToL1_eq_setToL1SCLM, setToL1_unique
-/
theorem setToL1_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : Real)
    (h_smul : forall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s) (f : α ->₁[μ] E) :
    setToL1 hT' f = c • setToL1 hT f := by
  apply setToL1_unique hT' (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left' c hT hT' h_smul]

/--
theorem `setToL1_smul` / 定理 `setToL1_smul`

English:
theorem setToL1_smul
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  rw [setToL1_eq_setToL1' hT h_smul]; rw [setToL1_eq_setToL1' hT h_smul]
  exact map_smul _ _ _

中文:
定理 setToL1_smul
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  rw [setToL1_eq_setToL1' hT h_smul]; rw [setToL1_eq_setToL1' hT h_smul]
  exact map_smul _ _ _

Depends on / 依赖: h_smul, map_smul, setToL1_eq_setToL1
-/
theorem setToL1_smul (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α ->₁[μ] E) :
    setToL1 hT (c • f) = c • setToL1 hT f := by
  rw [setToL1_eq_setToL1' hT h_smul]; rw [setToL1_eq_setToL1' hT h_smul]
  exact map_smul _ _ _

/--
theorem `setToL1_simpleFunc_indicatorConst` / 定理 `setToL1_simpleFunc_indicatorConst`

English:
theorem setToL1_simpleFunc_indicatorConst
  statement: (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
  proof: by
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1S_indicatorConst (fun s => hT.eq_zero_of_measure_zero) hT.1 hs hμs x

中文:
定理 setToL1_simpleFunc_indicatorConst
  结论: (hT : DominatedFinMeasAdditive μ T C) {s : 集合 α}
  证明: by
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1S_indicatorConst (fun s => hT.eq_zero_of_measure_zero) hT.1 hs hμs x

Depends on / 依赖: eq_zero_of_measure_zero, hT.eq_zero_of_measure_zero, setToL1S_indicatorConst, setToL1_eq_setToL1SCLM
-/
theorem setToL1_simpleFunc_indicatorConst (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) :
    setToL1 hT (simpleFunc.indicatorConst 1 hs hμs.ne x) = T s x := by
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1S_indicatorConst (fun s => hT.eq_zero_of_measure_zero) hT.1 hs hμs x

/--
theorem `setToL1_indicatorConstLp` / 定理 `setToL1_indicatorConstLp`

English:
theorem setToL1_indicatorConstLp
  statement: (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
  proof: by
  rw [← Lp.simpleFunc.coe_indicatorConst hs hμs x]
  exact setToL1_simpleFunc_indicatorConst hT hs hμs.lt_top x

中文:
定理 setToL1_indicatorConstLp
  结论: (hT : DominatedFinMeasAdditive μ T C) {s : 集合 α}
  证明: by
  rw [← Lp.simpleFunc.coe_indicatorConst hs hμs x]
  exact setToL1_simpleFunc_indicatorConst hT hs hμs.lt_top x

Depends on / 依赖: Lp.simpleFunc.coe_indicatorConst, coe_indicatorConst, lt_top, s.lt_top, setToL1_simpleFunc_indicatorConst, simpleFunc
-/
theorem setToL1_indicatorConstLp (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E) :
    setToL1 hT (indicatorConstLp 1 hs hμs x) = T s x := by
  rw [← Lp.simpleFunc.coe_indicatorConst hs hμs x]
  exact setToL1_simpleFunc_indicatorConst hT hs hμs.lt_top x

/--
theorem `setToL1_const` / 定理 `setToL1_const`

English:
theorem setToL1_const
  given: [IsFiniteMeasure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E)
  proof: setToL1_indicatorConstLp hT MeasurableSet.univ (measure_ne_top _ _) x

中文:
定理 setToL1_const
  条件: [是有限测度 μ] (hT : DominatedFinMeasAdditive μ T C) (x : E)
  证明: setToL1_indicatorConstLp hT MeasurableSet.univ (measure_ne_top _ _) x

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, measure_ne_top, setToL1_indicatorConstLp
-/
theorem setToL1_const [IsFiniteMeasure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    setToL1 hT (indicatorConstLp 1 MeasurableSet.univ (measure_ne_top _ _) x) = T univ x :=
  setToL1_indicatorConstLp hT MeasurableSet.univ (measure_ne_top _ _) x

section Order

variable {G' G'' : Type*}
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G'']
  [NormedSpace Real G''] [CompleteSpace G'']
  [NormedAddCommGroup G'] [PartialOrder G'] [NormedSpace Real G']

/--
theorem `setToL1_mono_left'` / 定理 `setToL1_mono_left'`

English:
theorem setToL1_mono_left'
  statement: [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
  proof: by
  induction f using Lp.induction (hp_ne_top := one_ne_top) with
  | @indicatorConst c s hs hμs =>
    rw [setToL1_simpleFunc_indicatorConst hT hs hμs]; rw [setToL1_simpleFunc_indicatorConst hT' hs hμs]
    exact hTT' s hs hμs c
  | @add f g hf hg _ hf_le hg_le =>
    rw [(setToL1 hT).map_add]; rw

中文:
定理 setToL1_mono_left'
  结论: [OrderClosed拓扑 G''] {T T' : 集合 α -> E ->L[实数] G''} {C C' : 实数}
  证明: by
  induction f using Lp.induction (hp_ne_top := one_ne_top) with
  | @indicatorConst c s hs hμs =>
    rw [setToL1_simpleFunc_indicatorConst hT hs hμs]; rw [setToL1_simpleFunc_indicatorConst hT' hs hμs]
    exact hTT' s hs hμs c
  | @add f g hf hg _ hf_le hg_le =>
    rw [(setToL1 hT).map_add]; rw

Depends on / 依赖: Lp.induction, add_le_add, continuous, hf_le, hg_le, hp_ne_top, indicatorConst, isClosed, isClosed_le, map_add, one_ne_top, setToL1, setToL1_simpleFunc_indicatorConst
-/
theorem setToL1_mono_left' [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x) (f : α ->₁[μ] E) :
    setToL1 hT f <= setToL1 hT' f := by
  induction f using Lp.induction (hp_ne_top := one_ne_top) with
  | @indicatorConst c s hs hμs =>
    rw [setToL1_simpleFunc_indicatorConst hT hs hμs]; rw [setToL1_simpleFunc_indicatorConst hT' hs hμs]
    exact hTT' s hs hμs c
  | @add f g hf hg _ hf_le hg_le =>
    rw [(setToL1 hT).map_add]; rw [(setToL1 hT').map_add]
    exact add_le_add hf_le hg_le
  | isClosed => exact isClosed_le (setToL1 hT).continuous (setToL1 hT').continuous

/--
theorem `setToL1_mono_left` / 定理 `setToL1_mono_left`

English:
theorem setToL1_mono_left
  statement: [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
  proof: setToL1_mono_left' hT hT' (fun s _ _ x => hTT' s x) f

中文:
定理 setToL1_mono_left
  结论: [OrderClosed拓扑 G''] {T T' : 集合 α -> E ->L[实数] G''} {C C' : 实数}
  证明: setToL1_mono_left' hT hT' (fun s _ _ x => hTT' s x) f

Depends on / 依赖: setToL1_mono_left
-/
theorem setToL1_mono_left [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : forall s x, T s x <= T' s x) (f : α ->₁[μ] E) : setToL1 hT f <= setToL1 hT' f :=
  setToL1_mono_left' hT hT' (fun s _ _ x => hTT' s x) f

/--
theorem `setToL1_nonneg` / 定理 `setToL1_nonneg`

English:
theorem setToL1_nonneg
  statement: [ClosedIciTopology G''] {T : Set α -> G' ->L[Real] G''} {C : Real}
  proof: by
  suffices forall f : { g : α ->₁[μ] G' // 0 <= g }, 0 <= setToL1 hT f from
    this (⟨f, hf⟩ : { g : α ->₁[μ] G' // 0 <= g })
  refine fun g =>
    @isClosed_property { g : α ->₁ₛ[μ] G' // 0 <= g } { g : α ->₁[μ] G' // 0 <= g } _ _
      (fun g => 0 <= setToL1 hT g)
      (denseRange_coeSimpleFu

中文:
定理 setToL1_nonneg
  结论: [ClosedIci拓扑 G''] {T : 集合 α -> G' ->L[实数] G''} {C : 实数}
  证明: by
  suffices forall f : { g : α ->₁[μ] G' // 0 <= g }, 0 <= setToL1 hT f from
    this (⟨f, hf⟩ : { g : α ->₁[μ] G' // 0 <= g })
  refine fun g =>
    @isClosed_property { g : α ->₁ₛ[μ] G' // 0 <= g } { g : α ->₁[μ] G' // 0 <= g } _ _
      (fun g => 0 <= setToL1 hT g)
      (denseRange_coeSimpleFu

Depends on / 依赖: coeSimpleFuncNonnegToLpNonneg, continuous, continuous.comp, continuous_induced_dom, denseRange_coeSimpleFuncNonnegToLpNonneg, isClosed_Ici, isClosed_property, one_ne_top, preimage, setToL1
-/
theorem setToL1_nonneg [ClosedIciTopology G''] {T : Set α -> G' ->L[Real] G''} {C : Real}
    (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f : α ->₁[μ] G'}
    (hf : 0 <= f) : 0 <= setToL1 hT f := by
  suffices forall f : { g : α ->₁[μ] G' // 0 <= g }, 0 <= setToL1 hT f from
    this (⟨f, hf⟩ : { g : α ->₁[μ] G' // 0 <= g })
  refine fun g =>
    @isClosed_property { g : α ->₁ₛ[μ] G' // 0 <= g } { g : α ->₁[μ] G' // 0 <= g } _ _
      (fun g => 0 <= setToL1 hT g)
      (denseRange_coeSimpleFuncNonnegToLpNonneg 1 μ G' one_ne_top) ?_ ?_ g
  · exact (isClosed_Ici (a := 0)).preimage ((setToL1 hT).continuous.comp continuous_induced_dom)
  · intro g
    have : (coeSimpleFuncNonnegToLpNonneg 1 μ G' g : α ->₁[μ] G') = (g : α ->₁ₛ[μ] G') := rfl
    rw [this]; rw [setToL1_eq_setToL1SCLM]
    exact setToL1S_nonneg (fun s => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg g.2

/--
theorem `setToL1_mono` / 定理 `setToL1_mono`

English:
theorem setToL1_mono
  statement: [ClosedIciTopology G''] [IsOrderedAddMonoid G']
  proof: by
  rw [← sub_nonneg] at hfg ⊢
  rw [← (setToL1 hT).map_sub]
  exact setToL1_nonneg hT hT_nonneg hfg

中文:
定理 setToL1_mono
  结论: [ClosedIci拓扑 G''] [是OrderedAdd幺半群 G']
  证明: by
  rw [← sub_nonneg] at hfg ⊢
  rw [← (setToL1 hT).map_sub]
  exact setToL1_nonneg hT hT_nonneg hfg

Depends on / 依赖: hT_nonneg, map_sub, setToL1, setToL1_nonneg, sub_nonneg
-/
theorem setToL1_mono [ClosedIciTopology G''] [IsOrderedAddMonoid G']
    {T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f g : α ->₁[μ] G'}
    (hfg : f <= g) : setToL1 hT f <= setToL1 hT g := by
  rw [← sub_nonneg] at hfg ⊢
  rw [← (setToL1 hT).map_sub]
  exact setToL1_nonneg hT hT_nonneg hfg

end Order

/--
theorem `norm_setToL1_le_norm_setToL1SCLM` / 定理 `norm_setToL1_le_norm_setToL1SCLM`

English:
theorem norm_setToL1_le_norm_setToL1SCLM
  given: (hT : DominatedFinMeasAdditive μ T C)
  proof: calc
    ‖setToL1 hT‖ <= (1 : Real>=0) * ‖setToL1SCLM α E μ hT‖ := by
      refine
        ContinuousLinearMap.opNorm_extend_le (setToL1SCLM α E μ hT)
          (simpleFunc.denseRange one_ne_top) fun x => le_of_eq ?_
      rw [NNReal.coe_one]; rw [one_mul]
      simp [coeToLp]
    _ = ‖setToL1SCLM α

中文:
定理 norm_setToL1_le_norm_setToL1SCLM
  条件: (hT : DominatedFinMeasAdditive μ T C)
  证明: calc
    ‖setToL1 hT‖ <= (1 : Real>=0) * ‖setToL1SCLM α E μ hT‖ := by
      refine
        ContinuousLinearMap.opNorm_extend_le (setToL1SCLM α E μ hT)
          (simpleFunc.denseRange one_ne_top) fun x => le_of_eq ?_
      rw [NNReal.coe_one]; rw [one_mul]
      simp [coeToLp]
    _ = ‖setToL1SCLM α

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_extend_le, NNReal, NNReal.coe_one, coeToLp, coe_one, denseRange, le_of_eq, one_mul, one_ne_top, opNorm_extend_le, setToL1, setToL1SCLM, simpleFunc, simpleFunc.denseRange
-/
theorem norm_setToL1_le_norm_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) :
    ‖setToL1 hT‖ <= ‖setToL1SCLM α E μ hT‖ :=
  calc
    ‖setToL1 hT‖ <= (1 : Real>=0) * ‖setToL1SCLM α E μ hT‖ := by
      refine
        ContinuousLinearMap.opNorm_extend_le (setToL1SCLM α E μ hT)
          (simpleFunc.denseRange one_ne_top) fun x => le_of_eq ?_
      rw [NNReal.coe_one]; rw [one_mul]
      simp [coeToLp]
    _ = ‖setToL1SCLM α E μ hT‖ := by rw [NNReal.coe_one, one_mul]

/--
theorem `norm_setToL1_le_mul_norm` / 定理 `norm_setToL1_le_mul_norm`

English:
theorem norm_setToL1_le_mul_norm
  statement: (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C)
  proof: calc
    ‖setToL1 hT f‖ <= ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ <= C * ‖f‖ := mul_le_mul (norm_setToL1SCLM_le hT hC) le_rfl (norm_nonneg _) hC

中文:
定理 norm_setToL1_le_mul_norm
  结论: (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C)
  证明: calc
    ‖setToL1 hT f‖ <= ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ <= C * ‖f‖ := mul_le_mul (norm_setToL1SCLM_le hT hC) le_rfl (norm_nonneg _) hC

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.le_of_opNorm_le, le_of_opNorm_le, le_rfl, mul_le_mul, norm_nonneg, norm_setToL1SCLM_le, norm_setToL1_le_norm_setToL1SCLM, setToL1, setToL1SCLM
-/
theorem norm_setToL1_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C)
    (f : α ->₁[μ] E) : ‖setToL1 hT f‖ <= C * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ <= ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ <= C * ‖f‖ := mul_le_mul (norm_setToL1SCLM_le hT hC) le_rfl (norm_nonneg _) hC

/--
theorem `norm_setToL1_le_mul_norm'` / 定理 `norm_setToL1_le_mul_norm'`

English:
theorem norm_setToL1_le_mul_norm'
  given: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E)
  proof: calc
    ‖setToL1 hT f‖ <= ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ <= max C 0 * ‖f‖ :=
      mul_le_mul (norm_setToL1SCLM_le' hT) le_rfl (norm_nonneg _) (le_max_right _ _)

中文:
定理 norm_setToL1_le_mul_norm'
  条件: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E)
  证明: calc
    ‖setToL1 hT f‖ <= ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ <= max C 0 * ‖f‖ :=
      mul_le_mul (norm_setToL1SCLM_le' hT) le_rfl (norm_nonneg _) (le_max_right _ _)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.le_of_opNorm_le, le_max_right, le_of_opNorm_le, le_rfl, mul_le_mul, norm_nonneg, norm_setToL1SCLM_le, norm_setToL1_le_norm_setToL1SCLM, setToL1, setToL1SCLM
-/
theorem norm_setToL1_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) :
    ‖setToL1 hT f‖ <= max C 0 * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ <= ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ <= max C 0 * ‖f‖ :=
      mul_le_mul (norm_setToL1SCLM_le' hT) le_rfl (norm_nonneg _) (le_max_right _ _)

/--
theorem `norm_setToL1_le` / 定理 `norm_setToL1_le`

English:
theorem norm_setToL1_le
  given: (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C)
  statement: ‖setToL1 hT‖ <= C
  proof: ContinuousLinearMap.opNorm_le_bound _ hC (norm_setToL1_le_mul_norm hT hC)

中文:
定理 norm_setToL1_le
  条件: (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C)
  结论: ‖setToL1 hT‖ <= C
  证明: ContinuousLinearMap.opNorm_le_bound _ hC (norm_setToL1_le_mul_norm hT hC)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, norm_setToL1_le_mul_norm, opNorm_le_bound
-/
theorem norm_setToL1_le (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) : ‖setToL1 hT‖ <= C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_setToL1_le_mul_norm hT hC)

/--
theorem `norm_setToL1_le'` / 定理 `norm_setToL1_le'`

English:
theorem norm_setToL1_le'
  given: (hT : DominatedFinMeasAdditive μ T C)
  statement: ‖setToL1 hT‖ <= max C 0
  proof: ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) (norm_setToL1_le_mul_norm' hT)

中文:
定理 norm_setToL1_le'
  条件: (hT : DominatedFinMeasAdditive μ T C)
  结论: ‖setToL1 hT‖ <= 最大值 C 0
  证明: ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) (norm_setToL1_le_mul_norm' hT)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, le_max_right, norm_setToL1_le_mul_norm, opNorm_le_bound
-/
theorem norm_setToL1_le' (hT : DominatedFinMeasAdditive μ T C) : ‖setToL1 hT‖ <= max C 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) (norm_setToL1_le_mul_norm' hT)

/--
theorem `setToL1_lipschitz` / 定理 `setToL1_lipschitz`

English:
theorem setToL1_lipschitz
  given: (hT : DominatedFinMeasAdditive μ T C)
  proof: (setToL1 hT).lipschitz.weaken (norm_setToL1_le' hT)

中文:
定理 setToL1_lipschitz
  条件: (hT : DominatedFinMeasAdditive μ T C)
  证明: (setToL1 hT).lipschitz.weaken (norm_setToL1_le' hT)

Depends on / 依赖: lipschitz, lipschitz.weaken, norm_setToL1_le, setToL1, weaken
-/
theorem setToL1_lipschitz (hT : DominatedFinMeasAdditive μ T C) :
    LipschitzWith (Real.toNNReal C) (setToL1 hT) :=
  (setToL1 hT).lipschitz.weaken (norm_setToL1_le' hT)

/--
theorem `tendsto_setToL1` / 定理 `tendsto_setToL1`

English:
theorem tendsto_setToL1
  statement: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) {ι}
  proof: ((setToL1 hT).continuous.tendsto _).comp hfs

中文:
定理 tendsto_setToL1
  结论: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) {ι}
  证明: ((setToL1 hT).continuous.tendsto _).comp hfs

Depends on / 依赖: continuous, continuous.tendsto, setToL1, tendsto
-/
theorem tendsto_setToL1 (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) {ι}
    (fs : ι -> α ->₁[μ] E) {l : Filter ι} (hfs : Tendsto fs l (𝓝 f)) :
    Tendsto (fun i => setToL1 hT (fs i)) l (𝓝 <| setToL1 hT f) :=
  ((setToL1 hT).continuous.tendsto _).comp hfs

end SetToL1

end L1

section Function

variable {T T' T'' : Set α -> E ->L[Real] F} {C C' C'' : Real} {f g : α -> E}
variable (μ T)

open scoped Classical in
/--
Definition of `setToFun` / `setToFun` 的定义

English:
definition setToFun
  signature: (hT : DominatedFinMeasAdditive μ T C) (f : α -> E)
  body: if _hF : CompleteSpace F then
    if hf : Integrable f μ then L1.setToL1 hT (hf.toL1 f) else 0
  else 0

中文:
定义 setToFun
  签名: (hT : DominatedFinMeasAdditive μ T C) (f : α -> E)
  定义体: if _hF : CompleteSpace F then
    if hf : Integrable f μ then L1.setToL1 hT (hf.toL1 f) else 0
  else 0

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1, hf.toL1, setToL1
-/
def setToFun (hT : DominatedFinMeasAdditive μ T C) (f : α -> E) : F :=
  if _hF : CompleteSpace F then
    if hf : Integrable f μ then L1.setToL1 hT (hf.toL1 f) else 0
  else 0

variable {μ T}

/--
theorem `setToFun_eq` / 定理 `setToFun_eq`

English:
theorem setToFun_eq
  statement: [hF : CompleteSpace F]
  proof: by
  simp [setToFun, hF, hf]

中文:
定理 setToFun_eq
  结论: [hF : 完备空间 F]
  证明: by
  simp [setToFun, hF, hf]

Depends on / 依赖: setToFun
-/
theorem setToFun_eq [hF : CompleteSpace F]
    (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    setToFun μ T hT f = L1.setToL1 hT (hf.toL1 f) := by
  simp [setToFun, hF, hf]

/--
theorem `L1.setToFun_eq_setToL1` / 定理 `L1.setToFun_eq_setToL1`

English:
theorem L1.setToFun_eq_setToL1
  statement: [CompleteSpace F]
  proof: by
  rw [setToFun_eq hT (L1.integrable_coeFn f)]; rw [Integrable.toL1_coeFn]

中文:
定理 L1.setToFun_eq_setToL1
  结论: [完备空间 F]
  证明: by
  rw [setToFun_eq hT (L1.integrable_coeFn f)]; rw [Integrable.toL1_coeFn]

Depends on / 依赖: Integrable, Integrable.toL1_coeFn, L1.integrable_coeFn, integrable_coeFn, setToFun_eq, toL1_coeFn
-/
theorem L1.setToFun_eq_setToL1 [CompleteSpace F]
    (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) :
    setToFun μ T hT f = L1.setToL1 hT f := by
  rw [setToFun_eq hT (L1.integrable_coeFn f)]; rw [Integrable.toL1_coeFn]

/--
theorem `setToFun_undef` / 定理 `setToFun_undef`

English:
theorem setToFun_undef
  given: (hT : DominatedFinMeasAdditive μ T C) (hf : ¬Integrable f μ)
  proof: by
  by_cases hF : CompleteSpace F
  · simp [setToFun, hF, hf]
  · simp [setToFun, hF]

中文:
定理 setToFun_undef
  条件: (hT : DominatedFinMeasAdditive μ T C) (hf : ¬可积 f μ)
  证明: by
  by_cases hF : CompleteSpace F
  · simp [setToFun, hF, hf]
  · simp [setToFun, hF]

Depends on / 依赖: CompleteSpace, setToFun
-/
theorem setToFun_undef (hT : DominatedFinMeasAdditive μ T C) (hf : ¬Integrable f μ) :
    setToFun μ T hT f = 0 := by
  by_cases hF : CompleteSpace F
  · simp [setToFun, hF, hf]
  · simp [setToFun, hF]

/--
theorem `setToFun_non_aestronglyMeasurable` / 定理 `setToFun_non_aestronglyMeasurable`

English:
theorem setToFun_non_aestronglyMeasurable
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: setToFun_undef hT (not_and_of_not_left _ hf)

中文:
定理 setToFun_non_aestronglyMeasurable
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: setToFun_undef hT (not_and_of_not_left _ hf)

Depends on / 依赖: not_and_of_not_left, setToFun_undef
-/
theorem setToFun_non_aestronglyMeasurable (hT : DominatedFinMeasAdditive μ T C)
    (hf : ¬AEStronglyMeasurable f μ) : setToFun μ T hT f = 0 :=
  setToFun_undef hT (not_and_of_not_left _ hf)

/--
theorem `setToFun_congr_left` / 定理 `setToFun_congr_left`

English:
theorem setToFun_congr_left
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]

中文:
定理 setToFun_congr_left
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_congr_left, setToFun, setToFun_eq, setToFun_undef, setToL1_congr_left, simp_rw
-/
theorem setToFun_congr_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T') (f : α -> E) :
    setToFun μ T hT f = setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]

/--
theorem `setToFun_congr_left'` / 定理 `setToFun_congr_left'`

English:
theorem setToFun_congr_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left' T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]

中文:
定理 setToFun_congr_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left' T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_congr_left, setToFun, setToFun_eq, setToFun_undef, setToL1_congr_left, simp_rw
-/
theorem setToFun_congr_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : forall s, MeasurableSet s -> μ s < ∞ -> T s = T' s)
    (f : α -> E) : setToFun μ T hT f = setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left' T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]

/--
theorem `setToFun_add_left` / 定理 `setToFun_add_left`

English:
theorem setToFun_add_left
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left hT hT']
  · simp_rw [setToFun_undef _ hf, add_zero]

中文:
定理 setToFun_add_left
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left hT hT']
  · simp_rw [setToFun_undef _ hf, add_zero]

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_add_left, add_zero, setToFun, setToFun_eq, setToFun_undef, setToL1_add_left, simp_rw
-/
theorem setToFun_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α -> E) :
    setToFun μ (T + T') (hT.add hT') f = setToFun μ T hT f + setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left hT hT']
  · simp_rw [setToFun_undef _ hf, add_zero]

/--
theorem `setToFun_add_left'` / 定理 `setToFun_add_left'`

English:
theorem setToFun_add_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left' hT hT' hT'' h_add]
  · simp_rw [setToFun_undef _ hf, add_zero]

中文:
定理 setToFun_add_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left' hT hT' hT'' h_add]
  · simp_rw [setToFun_undef _ hf, add_zero]

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_add_left, add_zero, h_add, setToFun, setToFun_eq, setToFun_undef, setToL1_add_left, simp_rw
-/
theorem setToFun_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : forall s, MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) (f : α -> E) :
    setToFun μ T'' hT'' f = setToFun μ T hT f + setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left' hT hT' hT'' h_add]
  · simp_rw [setToFun_undef _ hf, add_zero]

/--
theorem `setToFun_smul_left` / 定理 `setToFun_smul_left`

English:
theorem setToFun_smul_left
  given: (hT : DominatedFinMeasAdditive μ T C) (c : Real) (f : α -> E)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left hT c]
  · simp_rw [setToFun_undef _ hf, smul_zero]

中文:
定理 setToFun_smul_left
  条件: (hT : DominatedFinMeasAdditive μ T C) (c : 实数) (f : α -> E)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left hT c]
  · simp_rw [setToFun_undef _ hf, smul_zero]

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_smul_left, setToFun, setToFun_eq, setToFun_undef, setToL1_smul_left, simp_rw, smul_zero
-/
theorem setToFun_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : Real) (f : α -> E) :
    setToFun μ (fun s => c • T s) (hT.smul c) f = c • setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left hT c]
  · simp_rw [setToFun_undef _ hf, smul_zero]

/--
theorem `setToFun_smul_left'` / 定理 `setToFun_smul_left'`

English:
theorem setToFun_smul_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left' hT hT' c h_smul]
  · simp_rw [setToFun_undef _ hf, smul_zero]

@[simp]

中文:
定理 setToFun_smul_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left' hT hT' c h_smul]
  · simp_rw [setToFun_undef _ hf, smul_zero]

@[simp]

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_smul_left, h_smul, setToFun, setToFun_eq, setToFun_undef, setToL1_smul_left, simp_rw, smul_zero
-/
theorem setToFun_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : Real)
    (h_smul : forall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s) (f : α -> E) :
    setToFun μ T' hT' f = c • setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left' hT hT' c h_smul]
  · simp_rw [setToFun_undef _ hf, smul_zero]

@[simp]
/--
theorem `setToFun_zero` / 定理 `setToFun_zero`

English:
theorem setToFun_zero
  given: (hT : DominatedFinMeasAdditive μ T C)
  statement: setToFun μ T hT (0 : α -> E) = 0
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (integrable_zero _ _ _)]; rw [Integrable.toL1_zero]; rw [map_zero]

@[simp]

中文:
定理 setToFun_zero
  条件: (hT : DominatedFinMeasAdditive μ T C)
  结论: setToFun μ T hT (0 : α -> E) = 0
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (integrable_zero _ _ _)]; rw [Integrable.toL1_zero]; rw [map_zero]

@[simp]

Depends on / 依赖: CompleteSpace, Integrable, Integrable.toL1_zero, integrable_zero, map_zero, setToFun, setToFun_eq, toL1_zero
-/
theorem setToFun_zero (hT : DominatedFinMeasAdditive μ T C) : setToFun μ T hT (0 : α -> E) = 0 := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (integrable_zero _ _ _)]; rw [Integrable.toL1_zero]; rw [map_zero]

@[simp]
/--
theorem `setToFun_zero_left` / 定理 `setToFun_zero_left`

English:
theorem setToFun_zero_left
  given: {hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Real] F) C}
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left hT _
  · exact setToFun_undef hT hf

中文:
定理 setToFun_zero_left
  条件: {hT : DominatedFinMeasAdditive μ (0 : 集合 α -> E ->L[实数] F) C}
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left hT _
  · exact setToFun_undef hT hf

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_zero_left, setToFun, setToFun_eq, setToFun_undef, setToL1_zero_left
-/
theorem setToFun_zero_left {hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Real] F) C} :
    setToFun μ 0 hT f = 0 := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left hT _
  · exact setToFun_undef hT hf

/--
theorem `setToFun_zero_left'` / 定理 `setToFun_zero_left'`

English:
theorem setToFun_zero_left'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left' hT h_zero _
  · exact setToFun_undef hT hf

中文:
定理 setToFun_zero_left'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left' hT h_zero _
  · exact setToFun_undef hT hf

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_zero_left, h_zero, setToFun, setToFun_eq, setToFun_undef, setToL1_zero_left
-/
theorem setToFun_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0) : setToFun μ T hT f = 0 := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left' hT h_zero _
  · exact setToFun_undef hT hf

/--
theorem `setToFun_add` / 定理 `setToFun_add`

English:
theorem setToFun_add
  statement: (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (hf.add hg)]; rw [setToFun_eq hT hf]; rw [setToFun_eq hT hg]; rw [Integrable.toL1_add]; rw [(L1.setToL1 hT).map_add]

中文:
定理 setToFun_add
  结论: (hT : DominatedFinMeasAdditive μ T C) (hf : 可积 f μ)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (hf.add hg)]; rw [setToFun_eq hT hf]; rw [setToFun_eq hT hg]; rw [Integrable.toL1_add]; rw [(L1.setToL1 hT).map_add]

Depends on / 依赖: CompleteSpace, Integrable, Integrable.toL1_add, L1.setToL1, hf.add, map_add, setToFun, setToFun_eq, setToL1, toL1_add
-/
theorem setToFun_add (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ T hT g := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (hf.add hg)]; rw [setToFun_eq hT hf]; rw [setToFun_eq hT hg]; rw [Integrable.toL1_add]; rw [(L1.setToL1 hT).map_add]

/--
theorem `setToFun_finsetSum'` / 定理 `setToFun_finsetSum'`

English:
theorem setToFun_finsetSum'
  statement: (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι)
  proof: by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [setToFun_zero, Finset.sum_empty]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    rw [setToFun_add hT (hf i (Finset.mem_insert_self i s)) _]
    · rw [ih fun i hi => hf i (Fins

中文:
定理 setToFun_finsetSum'
  结论: (hT : DominatedFinMeasAdditive μ T C) {ι} (s : 有限集 ι)
  证明: by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [setToFun_zero, Finset.sum_empty]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    rw [setToFun_add hT (hf i (Finset.mem_insert_self i s)) _]
    · rw [ih fun i hi => hf i (Fins

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.sum_empty, Finset.sum_insert, classical, convert, induction_on, integrable_finsetSum, mem_insert_of_mem, mem_insert_self, not_false_iff, revert, setToFun_add, setToFun_zero, sum_empty, sum_insert
-/
theorem setToFun_finsetSum' (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι)
    {f : ι -> α -> E} (hf : forall i in s, Integrable (f i) μ) :
    setToFun μ T hT (∑ i in s, f i) = ∑ i in s, setToFun μ T hT (f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [setToFun_zero, Finset.sum_empty]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    rw [setToFun_add hT (hf i (Finset.mem_insert_self i s)) _]
    · rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
    · convert! integrable_finsetSum s fun i hi => hf i (Finset.mem_insert_of_mem hi) with x
      simp

@[deprecated (since := "2026-04-08")] alias setToFun_finset_sum' := setToFun_finsetSum'

/--
theorem `setToFun_finsetSum` / 定理 `setToFun_finsetSum`

English:
theorem setToFun_finsetSum
  statement: (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι) {f : ι -> α -> E}
  proof: by
  convert! setToFun_finsetSum' hT s hf with a; simp

@[deprecated (since := "2026-04-08")] alias setToFun_finset_sum := setToFun_finsetSum

中文:
定理 setToFun_finsetSum
  结论: (hT : DominatedFinMeasAdditive μ T C) {ι} (s : 有限集 ι) {f : ι -> α -> E}
  证明: by
  convert! setToFun_finsetSum' hT s hf with a; simp

@[deprecated (since := "2026-04-08")] alias setToFun_finset_sum := setToFun_finsetSum

Depends on / 依赖: convert, setToFun_finsetSum
-/
theorem setToFun_finsetSum (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι) {f : ι -> α -> E}
    (hf : forall i in s, Integrable (f i) μ) :
    (setToFun μ T hT fun a => ∑ i in s, f i a) = ∑ i in s, setToFun μ T hT (f i) := by
  convert! setToFun_finsetSum' hT s hf with a; simp

@[deprecated (since := "2026-04-08")] alias setToFun_finset_sum := setToFun_finsetSum

/--
theorem `setToFun_neg` / 定理 `setToFun_neg`

English:
theorem setToFun_neg
  given: (hT : DominatedFinMeasAdditive μ T C) (f : α -> E)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT hf.neg, Integrable.toL1_neg,
      (L1.setToL1 hT).map_neg]
  · rw [setToFun_undef hT hf, setToFun_undef hT, neg_zero]
    rwa [← integrable_neg_iff] at hf

中文:
定理 setToFun_neg
  条件: (hT : DominatedFinMeasAdditive μ T C) (f : α -> E)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT hf.neg, Integrable.toL1_neg,
      (L1.setToL1 hT).map_neg]
  · rw [setToFun_undef hT hf, setToFun_undef hT, neg_zero]
    rwa [← integrable_neg_iff] at hf

Depends on / 依赖: CompleteSpace, Integrable, Integrable.toL1_neg, L1.setToL1, hf.neg, integrable_neg_iff, map_neg, neg_zero, setToFun, setToFun_eq, setToFun_undef, setToL1, toL1_neg
-/
theorem setToFun_neg (hT : DominatedFinMeasAdditive μ T C) (f : α -> E) :
    setToFun μ T hT (-f) = -setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT hf.neg, Integrable.toL1_neg,
      (L1.setToL1 hT).map_neg]
  · rw [setToFun_undef hT hf, setToFun_undef hT, neg_zero]
    rwa [← integrable_neg_iff] at hf

/--
theorem `setToFun_neg'` / 定理 `setToFun_neg'`

English:
theorem setToFun_neg'
  given: (hT : DominatedFinMeasAdditive μ T C) (f : α -> E)
  proof: by
  simpa using setToFun_smul_left' hT hT.neg (-1) (by simp) f

中文:
定理 setToFun_neg'
  条件: (hT : DominatedFinMeasAdditive μ T C) (f : α -> E)
  证明: by
  simpa using setToFun_smul_left' hT hT.neg (-1) (by simp) f

Depends on / 依赖: hT.neg, setToFun_smul_left
-/
theorem setToFun_neg' (hT : DominatedFinMeasAdditive μ T C) (f : α -> E) :
    setToFun μ (-T) hT.neg f = -setToFun μ T hT f := by
  simpa using setToFun_smul_left' hT hT.neg (-1) (by simp) f

/--
theorem `setToFun_sub` / 定理 `setToFun_sub`

English:
theorem setToFun_sub
  statement: (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [setToFun_add hT hf hg.neg]; rw [setToFun_neg hT g]

中文:
定理 setToFun_sub
  结论: (hT : DominatedFinMeasAdditive μ T C) (hf : 可积 f μ)
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [setToFun_add hT hf hg.neg]; rw [setToFun_neg hT g]

Depends on / 依赖: hg.neg, setToFun_add, setToFun_neg, sub_eq_add_neg
-/
theorem setToFun_sub (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ T hT g := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [setToFun_add hT hf hg.neg]; rw [setToFun_neg hT g]

/--
theorem `setToFun_smul` / 定理 `setToFun_smul`

English:
theorem setToFun_smul
  statement: [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT (hf.smul c), Integrable.toL1_smul' f hf,
      L1.setToL1_smul hT h_smul c]
  · by_cases hr : c = 0
    · rw [hr]; simp
    · have hf' : ¬Integrable (c • f) μ := 

中文:
定理 setToFun_smul
  结论: [NormedDivision环 𝕜] [模 𝕜 E] [NormSMul类 𝕜 E]
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT (hf.smul c), Integrable.toL1_smul' f hf,
      L1.setToL1_smul hT h_smul c]
  · by_cases hr : c = 0
    · rw [hr]; simp
    · have hf' : ¬Integrable (c • f) μ := 

Depends on / 依赖: CompleteSpace, Integrable, Integrable.toL1_smul, L1.setToL1_smul, h_smul, hf.smul, integrable_smul_iff, setToFun, setToFun_eq, setToFun_undef, setToL1_smul, smul_zero, toL1_smul
-/
theorem setToFun_smul [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [Module 𝕜 F] [NormSMulClass 𝕜 F]
    (hT : DominatedFinMeasAdditive μ T C) (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (c : 𝕜)
    (f : α -> E) : setToFun μ T hT (c • f) = c • setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT (hf.smul c), Integrable.toL1_smul' f hf,
      L1.setToL1_smul hT h_smul c]
  · by_cases hr : c = 0
    · rw [hr]; simp
    · have hf' : ¬Integrable (c • f) μ := by rwa [integrable_smul_iff hr f]
      rw [setToFun_undef hT hf]; rw [setToFun_undef hT hf']; rw [smul_zero]

/--
theorem `setToFun_congr_ae` / 定理 `setToFun_congr_ae`

English:
theorem setToFun_congr_ae
  given: (hT : DominatedFinMeasAdditive μ T C) (h : f =ᵐ[μ] g)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hfi : Integrable f μ
  · have hgi : Integrable g μ := hfi.congr h
    rw [setToFun_eq hT hfi]; rw [setToFun_eq hT hgi]; rw [(Integrable.toL1_eq_toL1_iff f g hfi hgi).2 h]
  · have hgi : ¬Integrable g μ := by rw [integrable_c

中文:
定理 setToFun_congr_ae
  条件: (hT : DominatedFinMeasAdditive μ T C) (h : f =ᵐ[μ] g)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hfi : Integrable f μ
  · have hgi : Integrable g μ := hfi.congr h
    rw [setToFun_eq hT hfi]; rw [setToFun_eq hT hgi]; rw [(Integrable.toL1_eq_toL1_iff f g hfi hgi).2 h]
  · have hgi : ¬Integrable g μ := by rw [integrable_c

Depends on / 依赖: CompleteSpace, Integrable, Integrable.toL1_eq_toL1_iff, hfi.congr, integrable_congr, setToFun, setToFun_eq, setToFun_undef, toL1_eq_toL1_iff
-/
theorem setToFun_congr_ae (hT : DominatedFinMeasAdditive μ T C) (h : f =ᵐ[μ] g) :
    setToFun μ T hT f = setToFun μ T hT g := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hfi : Integrable f μ
  · have hgi : Integrable g μ := hfi.congr h
    rw [setToFun_eq hT hfi]; rw [setToFun_eq hT hgi]; rw [(Integrable.toL1_eq_toL1_iff f g hfi hgi).2 h]
  · have hgi : ¬Integrable g μ := by rw [integrable_congr h] at hfi; exact hfi
    rw [setToFun_undef hT hfi]; rw [setToFun_undef hT hgi]

/--
theorem `setToFun_measure_zero` / 定理 `setToFun_measure_zero`

English:
theorem setToFun_measure_zero
  given: (hT : DominatedFinMeasAdditive μ T C) (h : μ = 0)
  proof: by
  have : f =ᵐ[μ] 0 := by simp [h, EventuallyEq]
  rw [setToFun_congr_ae hT this]; rw [setToFun_zero]

中文:
定理 setToFun_measure_zero
  条件: (hT : DominatedFinMeasAdditive μ T C) (h : μ = 0)
  证明: by
  have : f =ᵐ[μ] 0 := by simp [h, EventuallyEq]
  rw [setToFun_congr_ae hT this]; rw [setToFun_zero]

Depends on / 依赖: EventuallyEq, setToFun_congr_ae, setToFun_zero
-/
theorem setToFun_measure_zero (hT : DominatedFinMeasAdditive μ T C) (h : μ = 0) :
    setToFun μ T hT f = 0 := by
  have : f =ᵐ[μ] 0 := by simp [h, EventuallyEq]
  rw [setToFun_congr_ae hT this]; rw [setToFun_zero]

/--
theorem `setToFun_measure_zero'` / 定理 `setToFun_measure_zero'`

English:
theorem setToFun_measure_zero'
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: setToFun_zero_left' hT fun s hs hμs => hT.eq_zero_of_measure_zero hs (h s hs hμs)

中文:
定理 setToFun_measure_zero'
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: setToFun_zero_left' hT fun s hs hμs => hT.eq_zero_of_measure_zero hs (h s hs hμs)

Depends on / 依赖: eq_zero_of_measure_zero, hT.eq_zero_of_measure_zero, setToFun_zero_left
-/
theorem setToFun_measure_zero' (hT : DominatedFinMeasAdditive μ T C)
    (h : forall s, MeasurableSet s -> μ s < ∞ -> μ s = 0) : setToFun μ T hT f = 0 :=
  setToFun_zero_left' hT fun s hs hμs => hT.eq_zero_of_measure_zero hs (h s hs hμs)

/--
theorem `setToFun_toL1` / 定理 `setToFun_toL1`

English:
theorem setToFun_toL1
  given: (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
  proof: setToFun_congr_ae hT hf.coeFn_toL1

中文:
定理 setToFun_toL1
  条件: (hT : DominatedFinMeasAdditive μ T C) (hf : 可积 f μ)
  证明: setToFun_congr_ae hT hf.coeFn_toL1

Depends on / 依赖: coeFn_toL1, hf.coeFn_toL1, setToFun_congr_ae
-/
theorem setToFun_toL1 (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    setToFun μ T hT (hf.toL1 f) = setToFun μ T hT f :=
  setToFun_congr_ae hT hf.coeFn_toL1

/--
theorem `setToFun_indicator_const` / 定理 `setToFun_indicator_const`

English:
theorem setToFun_indicator_const
  statement: [CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
  proof: by
  rw [setToFun_congr_ae hT (@indicatorConstLp_coeFn _ _ _ 1 _ _ _ hs hμs x).symm]
  rw [L1.setToFun_eq_setToL1 hT]
  exact L1.setToL1_indicatorConstLp hT hs hμs x

中文:
定理 setToFun_indicator_const
  结论: [完备空间 F] (hT : DominatedFinMeasAdditive μ T C) {s : 集合 α}
  证明: by
  rw [setToFun_congr_ae hT (@indicatorConstLp_coeFn _ _ _ 1 _ _ _ hs hμs x).symm]
  rw [L1.setToFun_eq_setToL1 hT]
  exact L1.setToL1_indicatorConstLp hT hs hμs x

Depends on / 依赖: L1.setToFun_eq_setToL1, L1.setToL1_indicatorConstLp, indicatorConstLp_coeFn, setToFun_congr_ae, setToFun_eq_setToL1, setToL1_indicatorConstLp
-/
theorem setToFun_indicator_const [CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E) :
    setToFun μ T hT (s.indicator fun _ => x) = T s x := by
  rw [setToFun_congr_ae hT (@indicatorConstLp_coeFn _ _ _ 1 _ _ _ hs hμs x).symm]
  rw [L1.setToFun_eq_setToL1 hT]
  exact L1.setToL1_indicatorConstLp hT hs hμs x

/--
theorem `setToFun_const` / 定理 `setToFun_const`

English:
theorem setToFun_const
  statement: [CompleteSpace F] [IsFiniteMeasure μ]
  proof: by
  have : (fun _ : α => x) = Set.indicator univ fun _ => x := (indicator_univ _).symm
  rw [this]
  exact setToFun_indicator_const hT MeasurableSet.univ (measure_ne_top _ _) x

中文:
定理 setToFun_const
  结论: [完备空间 F] [是有限测度 μ]
  证明: by
  have : (fun _ : α => x) = Set.indicator univ fun _ => x := (indicator_univ _).symm
  rw [this]
  exact setToFun_indicator_const hT MeasurableSet.univ (measure_ne_top _ _) x

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Set.indicator, indicator, indicator_univ, measure_ne_top, setToFun_indicator_const
-/
theorem setToFun_const [CompleteSpace F] [IsFiniteMeasure μ]
    (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    (setToFun μ T hT fun _ => x) = T univ x := by
  have : (fun _ : α => x) = Set.indicator univ fun _ => x := (indicator_univ _).symm
  rw [this]
  exact setToFun_indicator_const hT MeasurableSet.univ (measure_ne_top _ _) x

/--
theorem `setToFun_simpleFunc` / 定理 `setToFun_simpleFunc`

English:
theorem setToFun_simpleFunc
  statement: [CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  have h'f : MemLp f 1 μ := memLp_one_iff_integrable.mpr hf
  let g := f.toLp h'f
  have A : f =ᵐ[μ] g := h'f.coeFn_toLp.symm
  rw [setToFun_congr_ae hT A]; rw [L1.setToFun_eq_setToL1 hT]; rw [L1.setToL1_eq_setToL1SCLM]
  apply (SimpleFunc.setToSimpleFunc_congr T (fun s => hT.eq_zero_of_measure_z

中文:
定理 setToFun_simpleFunc
  结论: [完备空间 F] (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  have h'f : MemLp f 1 μ := memLp_one_iff_integrable.mpr hf
  let g := f.toLp h'f
  have A : f =ᵐ[μ] g := h'f.coeFn_toLp.symm
  rw [setToFun_congr_ae hT A]; rw [L1.setToFun_eq_setToL1 hT]; rw [L1.setToL1_eq_setToL1SCLM]
  apply (SimpleFunc.setToSimpleFunc_congr T (fun s => hT.eq_zero_of_measure_z

Depends on / 依赖: L1.setToFun_eq_setToL1, L1.setToL1_eq_setToL1SCLM, Lp.simpleFunc.toSimpleFunc_eq_toFun, SimpleFunc, SimpleFunc.setToSimpleFunc_congr, coeFn_toLp, eq_zero_of_measure_zero, f.coeFn_toLp.symm, f.toLp, hT.eq_zero_of_measure_zero, memLp_one_iff_integrable, memLp_one_iff_integrable.mpr, setToFun_congr_ae, setToFun_eq_setToL1, setToL1_eq_setToL1SCLM, setToSimpleFunc_congr, simpleFunc, toSimpleFunc_eq_toFun
-/
theorem setToFun_simpleFunc [CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C)
    (f : SimpleFunc α E) (hf : Integrable f μ) :
    setToFun μ T hT f = ∑ x in f.range, T (f ⁻¹' {x}) x := by
  have h'f : MemLp f 1 μ := memLp_one_iff_integrable.mpr hf
  let g := f.toLp h'f
  have A : f =ᵐ[μ] g := h'f.coeFn_toLp.symm
  rw [setToFun_congr_ae hT A]; rw [L1.setToFun_eq_setToL1 hT]; rw [L1.setToL1_eq_setToL1SCLM]
  apply (SimpleFunc.setToSimpleFunc_congr T (fun s => hT.eq_zero_of_measure_zero) hT.1 hf _).symm
  grw [A, Lp.simpleFunc.toSimpleFunc_eq_toFun]

/--
theorem `setToFun_simpleFunc_eq_setToSimpleFunc` / 定理 `setToFun_simpleFunc_eq_setToSimpleFunc`

English:
theorem setToFun_simpleFunc_eq_setToSimpleFunc
  statement: [CompleteSpace F]
  proof: by
  rw [setToFun_simpleFunc hT f hf]
  rfl

中文:
定理 setToFun_simpleFunc_eq_setToSimpleFunc
  结论: [完备空间 F]
  证明: by
  rw [setToFun_simpleFunc hT f hf]
  rfl

Depends on / 依赖: setToFun_simpleFunc
-/
theorem setToFun_simpleFunc_eq_setToSimpleFunc [CompleteSpace F]
    (hT : DominatedFinMeasAdditive μ T C) (f : SimpleFunc α E) (hf : Integrable f μ) :
    setToFun μ T hT f = f.setToSimpleFunc T := by
  rw [setToFun_simpleFunc hT f hf]
  rfl

section Order

variable {G' G'' : Type*}
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G'']
  [NormedSpace Real G'']
  [NormedAddCommGroup G'] [PartialOrder G'] [NormedSpace Real G']

/--
theorem `setToFun_mono_left'` / 定理 `setToFun_mono_left'`

English:
theorem setToFun_mono_left'
  statement: [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
  proof: by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf]; exact L1.setToL1_mono_left' hT hT' hTT' _
  · simp_rw [setToFun_undef _ hf, le_rfl]

中文:
定理 setToFun_mono_left'
  结论: [OrderClosed拓扑 G''] {T T' : 集合 α -> E ->L[实数] G''} {C C' : 实数}
  证明: by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf]; exact L1.setToL1_mono_left' hT hT' hTT' _
  · simp_rw [setToFun_undef _ hf, le_rfl]

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_mono_left, le_rfl, setToFun, setToFun_eq, setToFun_undef, setToL1_mono_left, simp_rw
-/
theorem setToFun_mono_left' [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x) (f : α -> E) :
    setToFun μ T hT f <= setToFun μ T' hT' f := by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf]; exact L1.setToL1_mono_left' hT hT' hTT' _
  · simp_rw [setToFun_undef _ hf, le_rfl]

/--
theorem `setToFun_mono_left` / 定理 `setToFun_mono_left`

English:
theorem setToFun_mono_left
  statement: [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
  proof: setToFun_mono_left' hT hT' (fun s _ _ x => hTT' s x) f

中文:
定理 setToFun_mono_left
  结论: [OrderClosed拓扑 G''] {T T' : 集合 α -> E ->L[实数] G''} {C C' : 实数}
  证明: setToFun_mono_left' hT hT' (fun s _ _ x => hTT' s x) f

Depends on / 依赖: setToFun_mono_left
-/
theorem setToFun_mono_left [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : forall s x, T s x <= T' s x) (f : α ->₁[μ] E) : setToFun μ T hT f <= setToFun μ T' hT' f :=
  setToFun_mono_left' hT hT' (fun s _ _ x => hTT' s x) f

/--
theorem `setToFun_nonneg` / 定理 `setToFun_nonneg`

English:
theorem setToFun_nonneg
  statement: [ClosedIciTopology G''] {T : Set α -> G' ->L[Real] G''} {C : Real}
  proof: by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hfi : Integrable f μ
  · simp_rw [setToFun_eq _ hfi]
    exact L1.setToL1_nonneg hT hT_nonneg hf
  · simp_rw [setToFun_undef _ hfi, le_rfl]

中文:
定理 setToFun_nonneg
  结论: [ClosedIci拓扑 G''] {T : 集合 α -> G' ->L[实数] G''} {C : 实数}
  证明: by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hfi : Integrable f μ
  · simp_rw [setToFun_eq _ hfi]
    exact L1.setToL1_nonneg hT hT_nonneg hf
  · simp_rw [setToFun_undef _ hfi, le_rfl]

Depends on / 依赖: CompleteSpace, Integrable, L1.setToL1_nonneg, hT_nonneg, le_rfl, setToFun, setToFun_eq, setToFun_undef, setToL1_nonneg, simp_rw
-/
theorem setToFun_nonneg [ClosedIciTopology G''] {T : Set α -> G' ->L[Real] G''} {C : Real}
    (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f : α -> G'}
    (hf : 0 <=ᵐ[μ] f) : 0 <= setToFun μ T hT f := by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hfi : Integrable f μ
  · simp_rw [setToFun_eq _ hfi]
    exact L1.setToL1_nonneg hT hT_nonneg hf
  · simp_rw [setToFun_undef _ hfi, le_rfl]

/--
theorem `setToFun_mono` / 定理 `setToFun_mono`

English:
theorem setToFun_mono
  statement: [ClosedIciTopology G''] [IsOrderedAddMonoid G']
  proof: by
  rw [← sub_nonneg]; rw [← setToFun_sub hT hg hf]
  refine setToFun_nonneg hT hT_nonneg (hfg.mono fun a ha => ?_)
  rw [Pi.sub_apply]; rw [Pi.zero_apply]; rw [sub_nonneg]
  exact ha

中文:
定理 setToFun_mono
  结论: [ClosedIci拓扑 G''] [是OrderedAdd幺半群 G']
  证明: by
  rw [← sub_nonneg]; rw [← setToFun_sub hT hg hf]
  refine setToFun_nonneg hT hT_nonneg (hfg.mono fun a ha => ?_)
  rw [Pi.sub_apply]; rw [Pi.zero_apply]; rw [sub_nonneg]
  exact ha

Depends on / 依赖: Pi.sub_apply, Pi.zero_apply, hT_nonneg, hfg.mono, setToFun_nonneg, setToFun_sub, sub_apply, sub_nonneg, zero_apply
-/
theorem setToFun_mono [ClosedIciTopology G''] [IsOrderedAddMonoid G']
    {T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f g : α -> G'}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f <=ᵐ[μ] g) :
    setToFun μ T hT f <= setToFun μ T hT g := by
  rw [← sub_nonneg]; rw [← setToFun_sub hT hg hf]
  refine setToFun_nonneg hT hT_nonneg (hfg.mono fun a ha => ?_)
  rw [Pi.sub_apply]; rw [Pi.zero_apply]; rw [sub_nonneg]
  exact ha

end Order

@[continuity]
/--
theorem `continuous_setToFun` / 定理 `continuous_setToFun`

English:
theorem continuous_setToFun
  given: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF, continuous_const]
  simp_rw [L1.setToFun_eq_setToL1 hT]; exact ContinuousLinearMap.continuous _

中文:
定理 continuous_setToFun
  条件: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF, continuous_const]
  simp_rw [L1.setToFun_eq_setToL1 hT]; exact ContinuousLinearMap.continuous _

Depends on / 依赖: CompleteSpace, ContinuousLinearMap, ContinuousLinearMap.continuous, L1.setToFun_eq_setToL1, continuous, continuous_const, setToFun, setToFun_eq_setToL1, simp_rw
-/
theorem continuous_setToFun (hT : DominatedFinMeasAdditive μ T C) :
    Continuous fun f : α ->₁[μ] E => setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF, continuous_const]
  simp_rw [L1.setToFun_eq_setToL1 hT]; exact ContinuousLinearMap.continuous _

/--
theorem `tendsto_setToFun_of_L1` / 定理 `tendsto_setToFun_of_L1`

English:
theorem tendsto_setToFun_of_L1
  statement: (hT : DominatedFinMeasAdditive μ T C) {ι} (f : α -> E)
  proof: by
  classical
  rcases eq_or_neBot l with rfl | hl
  · simp
  have hfi : Integrable f μ := by
    obtain ⟨i, hi, h'i⟩ : exists i, ∫⁻ x, ‖fs i x - f x‖ₑ ∂μ < 1 ∧ Integrable (fs i) μ :=
      (((tendsto_order.1 hfs).2 _ zero_lt_one).and hfsi).exists
    have : Integrable (fs i - f) μ := ⟨h'i.aestrong

中文:
定理 tendsto_setToFun_of_L1
  结论: (hT : DominatedFinMeasAdditive μ T C) {ι} (f : α -> E)
  证明: by
  classical
  rcases eq_or_neBot l with rfl | hl
  · simp
  have hfi : Integrable f μ := by
    obtain ⟨i, hi, h'i⟩ : exists i, ∫⁻ x, ‖fs i x - f x‖ₑ ∂μ < 1 ∧ Integrable (fs i) μ :=
      (((tendsto_order.1 hfs).2 _ zero_lt_one).and hfsi).exists
    have : Integrable (fs i - f) μ := ⟨h'i.aestrong

Depends on / 依赖: F_lp, Integrable, Lp.tends, Tendsto, aestronglyMeasurable, classical, convert, eq_or_neBot, f_lp, hFi.toL1, hfi.toL1, hi.trans, i.aestronglyMeasurable.sub, i.sub, one_lt_top, tendsto_L1, tendsto_order, zero_lt_one
-/
theorem tendsto_setToFun_of_L1 (hT : DominatedFinMeasAdditive μ T C) {ι} (f : α -> E)
    (hf : AEStronglyMeasurable f μ) {fs : ι -> α -> E} {l : Filter ι}
    (hfsi : forallᶠ i in l, Integrable (fs i) μ)
    (hfs : Tendsto (fun i => ∫⁻ x, ‖fs i x - f x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => setToFun μ T hT (fs i)) l (𝓝 <| setToFun μ T hT f) := by
  classical
  rcases eq_or_neBot l with rfl | hl
  · simp
  have hfi : Integrable f μ := by
    obtain ⟨i, hi, h'i⟩ : exists i, ∫⁻ x, ‖fs i x - f x‖ₑ ∂μ < 1 ∧ Integrable (fs i) μ :=
      (((tendsto_order.1 hfs).2 _ zero_lt_one).and hfsi).exists
    have : Integrable (fs i - f) μ := ⟨h'i.aestronglyMeasurable.sub hf, hi.trans one_lt_top⟩
    convert h'i.sub this
    abel
  let f_lp := hfi.toL1 f
  let F_lp i := if hFi : Integrable (fs i) μ then hFi.toL1 (fs i) else 0
  have tendsto_L1 : Tendsto F_lp l (𝓝 f_lp) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply]
    refine (tendsto_congr' ?_).mp hfs
    filter_upwards [hfsi] with i hi
    refine lintegral_congr_ae ?_
    filter_upwards [hi.coeFn_toL1, hfi.coeFn_toL1] with x hxi hxf
    simp_rw [F_lp, dif_pos hi, hxi, f_lp, hxf]
  suffices Tendsto (fun i => setToFun μ T hT (F_lp i)) l (𝓝 (setToFun μ T hT f)) by
    refine (tendsto_congr' ?_).mp this
    filter_upwards [hfsi] with i hi
    suffices h_ae_eq : F_lp i =ᵐ[μ] fs i from setToFun_congr_ae hT h_ae_eq
    simp_rw [F_lp, dif_pos hi]
    exact hi.coeFn_toL1
  rw [setToFun_congr_ae hT hfi.coeFn_toL1.symm]
  exact ((continuous_setToFun hT).tendsto f_lp).comp tendsto_L1

/--
theorem `tendsto_setToFun_approxOn_of_measurable` / 定理 `tendsto_setToFun_approxOn_of_measurable`

English:
theorem tendsto_setToFun_approxOn_of_measurable
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: tendsto_setToFun_of_L1 hT _ hfi.aestronglyMeasurable
    (Eventually.of_forall (SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i))
    (SimpleFunc.tendsto_approxOn_L1_enorm hfm _ hs (hfi.sub h₀i).2)

中文:
定理 tendsto_setToFun_approxOn_of_measurable
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: tendsto_setToFun_of_L1 hT _ hfi.aestronglyMeasurable
    (Eventually.of_forall (SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i))
    (SimpleFunc.tendsto_approxOn_L1_enorm hfm _ hs (hfi.sub h₀i).2)

Depends on / 依赖: Eventually, Eventually.of_forall, SimpleFunc, SimpleFunc.integrable_approxOn, SimpleFunc.tendsto_approxOn_L1_enorm, aestronglyMeasurable, hfi.aestronglyMeasurable, hfi.sub, integrable_approxOn, of_forall, tendsto_approxOn_L1_enorm, tendsto_setToFun_of_L1
-/
theorem tendsto_setToFun_approxOn_of_measurable (hT : DominatedFinMeasAdditive μ T C)
    [MeasurableSpace E] [BorelSpace E] {f : α -> E} {s : Set E} [SeparableSpace s]
    (hfi : Integrable f μ) (hfm : Measurable f) (hs : forallᵐ x ∂μ, f x in closure s) {y₀ : E}
    (h₀ : y₀ in s) (h₀i : Integrable (fun _ => y₀) μ) :
    Tendsto (fun n => setToFun μ T hT (SimpleFunc.approxOn f hfm s y₀ h₀ n)) atTop
      (𝓝 <| setToFun μ T hT f) :=
  tendsto_setToFun_of_L1 hT _ hfi.aestronglyMeasurable
    (Eventually.of_forall (SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i))
    (SimpleFunc.tendsto_approxOn_L1_enorm hfm _ hs (hfi.sub h₀i).2)

/--
theorem `tendsto_setToFun_approxOn_of_measurable_of_range_subset` / 定理 `tendsto_setToFun_approxOn_of_measurable_of_range_subset`

English:
theorem tendsto_setToFun_approxOn_of_measurable_of_range_subset
  proof: by
  refine tendsto_setToFun_approxOn_of_measurable hT hf fmeas ?_ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

中文:
定理 tendsto_setToFun_approxOn_of_measurable_of_range_subset
  证明: by
  refine tendsto_setToFun_approxOn_of_measurable hT hf fmeas ?_ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

Depends on / 依赖: Eventually, Eventually.of_forall, Set.mem_union_left, integrable_zero, mem_range_self, mem_union_left, of_forall, subset_closure, tendsto_setToFun_approxOn_of_measurable
-/
theorem tendsto_setToFun_approxOn_of_measurable_of_range_subset
    (hT : DominatedFinMeasAdditive μ T C) [MeasurableSpace E] [BorelSpace E] {f : α -> E}
    (fmeas : Measurable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s]
    (hs : range f union {0} subseteq s) :
    Tendsto (fun n => setToFun μ T hT (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n)) atTop
      (𝓝 <| setToFun μ T hT f) := by
  refine tendsto_setToFun_approxOn_of_measurable hT hf fmeas ?_ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

/--
theorem `setToFun_of_le_map_of_stronglyMeasurable` / 定理 `setToFun_of_le_map_of_stronglyMeasurable`

English:
theorem setToFun_of_le_map_of_stronglyMeasurable
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hfi' : Integrable f μ' :=
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hf).mono_measure hμ'
  borelize E
  have : SeparableSpace (range f union {0} : Set E) := hfm.separableSpace_range_union_singleton

中文:
定理 setToFun_of_le_map_of_stronglyMeasurable
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hfi' : Integrable f μ' :=
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hf).mono_measure hμ'
  borelize E
  have : SeparableSpace (range f union {0} : Set E) := hfm.separableSpace_range_union_singleton

Depends on / 依赖: CompleteSpace, Integrable, SeparableSpace, Subset, Subset.rfl, aemeasurable, aestronglyMeasurable, borelize, convert, hfm.aestronglyMeasurable, hfm.measurable, hfm.measurable.comp, hfm.separableSpace_range_union_singleton, integrable_map_measure, measurable, mono_measure, separableSpace_range_union_singleton, setToFun, tendsto_nhds_unique, tendsto_setToFun_approxOn_of_measurable_of_range_subset
-/
theorem setToFun_of_le_map_of_stronglyMeasurable
    (hT : DominatedFinMeasAdditive μ T C) {β : Type*} {_ : MeasurableSpace β}
    {μ' : Measure β} {φ : α -> β} {T' : Set β -> E ->L[Real] F} (hT' : DominatedFinMeasAdditive μ' T' C')
    {f : β -> E} (hf : Integrable (f ∘ φ) μ) (hfm : StronglyMeasurable f) (hφ : Measurable φ)
    (hμ' : μ' <= μ.map φ)
    (h : forall (s : Set β) (x : E), MeasurableSet s -> T' s x = T (φ ⁻¹' s) x) :
    setToFun μ' T' hT' f = setToFun μ T hT (f ∘ φ) := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hfi' : Integrable f μ' :=
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hf).mono_measure hμ'
  borelize E
  have : SeparableSpace (range f union {0} : Set E) := hfm.separableSpace_range_union_singleton
  refine tendsto_nhds_unique
    (tendsto_setToFun_approxOn_of_measurable_of_range_subset
      hT' hfm.measurable hfi' _ Subset.rfl) ?_
  convert tendsto_setToFun_approxOn_of_measurable_of_range_subset
    hT (hfm.measurable.comp hφ) hf (range f union {0})
    (union_subset_union_left {0} (range_comp_subset_range φ f)) using 1
  ext i : 1
  rw [setToFun_simpleFunc _ _ (SimpleFunc.integrable_approxOn_range _ hfi' _)]; rw [setToFun_simpleFunc]; rw [SimpleFunc.approxOn_comp hfm.measurable hφ]; swap
  · apply SimpleFunc.integrable_approxOn _ hf (by simp) (by simp)
  simp only [union_singleton, SimpleFunc.measurableSet_preimage, h, ← preimage_comp,
    SimpleFunc.coe_comp]
  refine (Finset.sum_subset (SimpleFunc.range_comp_subset_range _ hφ) fun y _ hy => ?_).symm
  rw [SimpleFunc.mem_range]; rw [← Set.preimage_singleton_eq_empty]; rw [SimpleFunc.coe_comp] at hy
  simp [hy, hT.1.map_empty_eq_zero]

/--
theorem `setToFun_of_le_map` / 定理 `setToFun_of_le_map`

English:
theorem setToFun_of_le_map
  proof: by
  let g := hfm.mk
  have A : setToFun μ' T' hT' f = setToFun μ' T' hT' g :=
    setToFun_congr_ae _ (ae_mono hμ' hfm.ae_eq_mk)
  have B : setToFun μ T hT (f ∘ φ) = setToFun μ T hT (g ∘ φ) := by
    apply setToFun_congr_ae
    exact ae_of_ae_map hφ.aemeasurable hfm.ae_eq_mk
  rw [A]; rw [B]
  exac

中文:
定理 setToFun_of_le_map
  证明: by
  let g := hfm.mk
  have A : setToFun μ' T' hT' f = setToFun μ' T' hT' g :=
    setToFun_congr_ae _ (ae_mono hμ' hfm.ae_eq_mk)
  have B : setToFun μ T hT (f ∘ φ) = setToFun μ T hT (g ∘ φ) := by
    apply setToFun_congr_ae
    exact ae_of_ae_map hφ.aemeasurable hfm.ae_eq_mk
  rw [A]; rw [B]
  exac

Depends on / 依赖: ae_eq_mk, ae_mono, ae_of_ae_map, aemeasurable, hf.congr, hfm.ae_eq_mk, hfm.mk, hfm.stronglyMeasurable_mk, setToFun, setToFun_congr_ae, setToFun_of_le_map_of_stronglyMeasurable, stronglyMeasurable_mk
-/
theorem setToFun_of_le_map
    (hT : DominatedFinMeasAdditive μ T C) {β : Type*} {_ : MeasurableSpace β}
    {μ' : Measure β} {φ : α -> β} {T' : Set β -> E ->L[Real] F} (hT' : DominatedFinMeasAdditive μ' T' C')
    {f : β -> E} (hf : Integrable (f ∘ φ) μ) (hfm : AEStronglyMeasurable f (μ.map φ))
    (hφ : Measurable φ) (hμ' : μ' <= μ.map φ)
    (h : forall (s : Set β) (x : E), MeasurableSet s -> T' s x = T (φ ⁻¹' s) x) :
    setToFun μ' T' hT' f = setToFun μ T hT (f ∘ φ) := by
  let g := hfm.mk
  have A : setToFun μ' T' hT' f = setToFun μ' T' hT' g :=
    setToFun_congr_ae _ (ae_mono hμ' hfm.ae_eq_mk)
  have B : setToFun μ T hT (f ∘ φ) = setToFun μ T hT (g ∘ φ) := by
    apply setToFun_congr_ae
    exact ae_of_ae_map hφ.aemeasurable hfm.ae_eq_mk
  rw [A]; rw [B]
  exact setToFun_of_le_map_of_stronglyMeasurable _ _
    (hf.congr (ae_of_ae_map hφ.aemeasurable hfm.ae_eq_mk)) hfm.stronglyMeasurable_mk hφ hμ' h

/--
theorem `continuous_L1_toL1` / 定理 `continuous_L1_toL1`

English:
theorem continuous_L1_toL1
  given: {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞) (hμ'_le : μ' <= c' • μ)
  proof: by
  by_cases hc'0 : c' = 0
  · have hμ'0 : μ' = 0 := by rw [← Measure.nonpos_iff_eq_zero']; refine hμ'_le.trans ?_; simp [hc'0]
    have h_im_zero :
      (fun f : α ->₁[μ] G =>
          (Integrable.of_measure_le_smul hc' hμ'_le (L1.integrable_coeFn f)).toL1 f) =
        0 := by
      ext1 f; ext1

中文:
定理 continuous_L1_toL1
  条件: {μ' : 测度 α} (c' : 实数>=0∞) (hc' : c' != ∞) (hμ'_le : μ' <= c' • μ)
  证明: by
  by_cases hc'0 : c' = 0
  · have hμ'0 : μ' = 0 := by rw [← Measure.nonpos_iff_eq_zero']; refine hμ'_le.trans ?_; simp [hc'0]
    have h_im_zero :
      (fun f : α ->₁[μ] G =>
          (Integrable.of_measure_le_smul hc' hμ'_le (L1.integrable_coeFn f)).toL1 f) =
        0 := by
      ext1 f; ext1

Depends on / 依赖: EventuallyEq, Integrable, Integrable.of_measure_le_smul, L1.integrable_coeFn, Measure, Measure.nonpos_iff_eq_zero, Metric, Metric.continuous_iff, _le.trans, ae_zero, continuous_iff, continuous_zero, div_pos, eventually_bot, h_im_zero, half_pos, integrable_coeFn, nonpos_iff_eq_zero, of_measure_le_smul, simp_rw
-/
theorem continuous_L1_toL1 {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞) (hμ'_le : μ' <= c' • μ) :
    Continuous fun f : α ->₁[μ] G =>
      (Integrable.of_measure_le_smul hc' hμ'_le (L1.integrable_coeFn f)).toL1 f := by
  by_cases hc'0 : c' = 0
  · have hμ'0 : μ' = 0 := by rw [← Measure.nonpos_iff_eq_zero']; refine hμ'_le.trans ?_; simp [hc'0]
    have h_im_zero :
      (fun f : α ->₁[μ] G =>
          (Integrable.of_measure_le_smul hc' hμ'_le (L1.integrable_coeFn f)).toL1 f) =
        0 := by
      ext1 f; ext1; simp_rw [hμ'0]; simp only [ae_zero, EventuallyEq, eventually_bot]
    rw [h_im_zero]
    exact continuous_zero
  rw [Metric.continuous_iff]
  intro f ε hε_pos
  use ε / 2 / c'.toReal
  refine ⟨div_pos (half_pos hε_pos) (toReal_pos hc'0 hc'), ?_⟩
  intro g hfg
  rw [Lp.dist_def] at hfg ⊢
  let h_int := fun f' : α ->₁[μ] G => (L1.integrable_coeFn f').of_measure_le_smul hc' hμ'_le
  have :
    eLpNorm (⇑(Integrable.toL1 g (h_int g)) - ⇑(Integrable.toL1 f (h_int f))) 1 μ' =
      eLpNorm (⇑g - ⇑f) 1 μ' :=
    eLpNorm_congr_ae ((Integrable.coeFn_toL1 _).sub (Integrable.coeFn_toL1 _))
  rw [this]
  have h_eLpNorm_ne_top : eLpNorm (⇑g - ⇑f) 1 μ != ∞ := by
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub _ _)]; exact Lp.eLpNorm_ne_top _
  calc
    (eLpNorm (⇑g - ⇑f) 1 μ').toReal <= (c' * eLpNorm (⇑g - ⇑f) 1 μ).toReal := by
      refine toReal_mono (ENNReal.mul_ne_top hc' h_eLpNorm_ne_top) ?_
      refine (eLpNorm_mono_measure (⇑g - ⇑f) hμ'_le).trans_eq ?_
      rw [eLpNorm_smul_measure_of_ne_zero hc'0]; rw [smul_eq_mul]
      simp
    _ = c'.toReal * (eLpNorm (⇑g - ⇑f) 1 μ).toReal := toReal_mul
    _ <= c'.toReal * (ε / 2 / c'.toReal) := by gcongr
    _ = ε / 2 := by
      refine mul_div_cancel₀ (ε / 2) ?_; rw [Ne, toReal_eq_zero_iff]; simp [hc', hc'0]
    _ < ε := half_lt_self hε_pos

/--
theorem `setToFun_congr_measure_of_integrable` / 定理 `setToFun_congr_measure_of_integrable`

English:
theorem setToFun_congr_measure_of_integrable
  statement: {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- integrability for `μ` implies integrability for `μ'`.
  have h_int : forall g : α -> E, Integrable g μ -> Integrable g μ' := fun g hg =>
    Integrable.of_measure_le_smul hc' hμ'_le hg
  -- We use `Integrable.induction`
  apply hf

中文:
定理 setToFun_congr_measure_of_integrable
  结论: {μ' : 测度 α} (c' : 实数>=0∞) (hc' : c' != ∞)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- integrability for `μ` implies integrability for `μ'`.
  have h_int : forall g : α -> E, Integrable g μ -> Integrable g μ' := fun g hg =>
    Integrable.of_measure_le_smul hc' hμ'_le hg
  -- We use `Integrable.induction`
  apply hf

Depends on / 依赖: CompleteSpace, setToFun
-/
theorem setToFun_congr_measure_of_integrable {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞)
    (hμ'_le : μ' <= c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α -> E) (hfμ : Integrable f μ) :
    setToFun μ T hT f = setToFun μ' T hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- integrability for `μ` implies integrability for `μ'`.
  have h_int : forall g : α -> E, Integrable g μ -> Integrable g μ' := fun g hg =>
    Integrable.of_measure_le_smul hc' hμ'_le hg
  -- We use `Integrable.induction`
  apply hfμ.induction (P := fun f => setToFun μ T hT f = setToFun μ' T hT' f)
  · intro c s hs hμs
    have hμ's : μ' s != ∞ := by
      refine ((hμ'_le s).trans_lt ?_).ne
      rw [Measure.smul_apply]; rw [smul_eq_mul]
      exact ENNReal.mul_lt_top hc'.lt_top hμs
    rw [setToFun_indicator_const hT hs hμs.ne]; rw [setToFun_indicator_const hT' hs hμ's]
  · intro f₂ g₂ _ hf₂ hg₂ h_eq_f h_eq_g
    rw [setToFun_add hT hf₂ hg₂]; rw [setToFun_add hT' (h_int f₂ hf₂) (h_int g₂ hg₂)]; rw [h_eq_f]; rw [h_eq_g]
  · refine isClosed_eq (continuous_setToFun hT) ?_
    have :
      (fun f : α ->₁[μ] E => setToFun μ' T hT' f) = fun f : α ->₁[μ] E =>
        setToFun μ' T hT' ((h_int f (L1.integrable_coeFn f)).toL1 f) := by
      ext1 f; exact setToFun_congr_ae hT' (Integrable.coeFn_toL1 _).symm
    rw [this]
    exact (continuous_setToFun hT').comp (continuous_L1_toL1 c' hc' hμ'_le)
  · intro f₂ g₂ hfg _ hf_eq
    have hfg' : f₂ =ᵐ[μ'] g₂ := (Measure.absolutelyContinuous_of_le_smul hμ'_le).ae_eq hfg
    rw [← setToFun_congr_ae hT hfg]; rw [hf_eq]; rw [setToFun_congr_ae hT' hfg']

/--
theorem `setToFun_congr_measure` / 定理 `setToFun_congr_measure`

English:
theorem setToFun_congr_measure
  statement: {μ' : Measure α} (c c' : Real>=0∞) (hc : c != ∞) (hc' : c' != ∞)
  proof: by
  by_cases hf : Integrable f μ
  · exact setToFun_congr_measure_of_integrable c' hc' hμ'_le hT hT' f hf
  · -- if `f` is not integrable, both `setToFun` are 0.
    have h_int : forall g : α -> E, ¬Integrable g μ -> ¬Integrable g μ' := fun g =>
      mt fun h => h.of_measure_le_smul hc hμ_le
    s

中文:
定理 setToFun_congr_measure
  结论: {μ' : 测度 α} (c c' : 实数>=0∞) (hc : c != ∞) (hc' : c' != ∞)
  证明: by
  by_cases hf : Integrable f μ
  · exact setToFun_congr_measure_of_integrable c' hc' hμ'_le hT hT' f hf
  · -- if `f` is not integrable, both `setToFun` are 0.
    have h_int : forall g : α -> E, ¬Integrable g μ -> ¬Integrable g μ' := fun g =>
      mt fun h => h.of_measure_le_smul hc hμ_le
    s

Depends on / 依赖: Integrable, h.of_measure_le_smul, h_int, integrable, of_measure_le_smul, setToFun, setToFun_congr_measure_of_integrable, setToFun_undef, simp_rw
-/
theorem setToFun_congr_measure {μ' : Measure α} (c c' : Real>=0∞) (hc : c != ∞) (hc' : c' != ∞)
    (hμ_le : μ <= c • μ') (hμ'_le : μ' <= c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α -> E) :
    setToFun μ T hT f = setToFun μ' T hT' f := by
  by_cases hf : Integrable f μ
  · exact setToFun_congr_measure_of_integrable c' hc' hμ'_le hT hT' f hf
  · -- if `f` is not integrable, both `setToFun` are 0.
    have h_int : forall g : α -> E, ¬Integrable g μ -> ¬Integrable g μ' := fun g =>
      mt fun h => h.of_measure_le_smul hc hμ_le
    simp_rw [setToFun_undef _ hf, setToFun_undef _ (h_int f hf)]

/--
theorem `setToFun_congr_measure_of_add_right` / 定理 `setToFun_congr_measure_of_add_right`

English:
theorem setToFun_congr_measure_of_add_right
  statement: {μ' : Measure α}
  proof: by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  nth_rw 1 [← add_zero μ]
  exact add_le_add le_rfl bot_le

中文:
定理 setToFun_congr_measure_of_add_right
  结论: {μ' : 测度 α}
  证明: by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  nth_rw 1 [← add_zero μ]
  exact add_le_add le_rfl bot_le

Depends on / 依赖: add_le_add, add_zero, bot_le, hT_add, le_rfl, nth_rw, one_ne_top, one_smul, setToFun_congr_measure_of_integrable
-/
theorem setToFun_congr_measure_of_add_right {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ T C)
    (f : α -> E) (hf : Integrable f (μ + μ')) :
    setToFun (μ + μ') T hT_add f = setToFun μ T hT f := by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  nth_rw 1 [← add_zero μ]
  exact add_le_add le_rfl bot_le

/--
theorem `setToFun_congr_measure_of_add_left` / 定理 `setToFun_congr_measure_of_add_left`

English:
theorem setToFun_congr_measure_of_add_left
  statement: {μ' : Measure α}
  proof: by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  exact Measure.le_add_left le_rfl

中文:
定理 setToFun_congr_measure_of_add_left
  结论: {μ' : 测度 α}
  证明: by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  exact Measure.le_add_left le_rfl

Depends on / 依赖: Measure, Measure.le_add_left, hT_add, le_add_left, le_rfl, one_ne_top, one_smul, setToFun_congr_measure_of_integrable
-/
theorem setToFun_congr_measure_of_add_left {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ' T C)
    (f : α -> E) (hf : Integrable f (μ + μ')) :
    setToFun (μ + μ') T hT_add f = setToFun μ' T hT f := by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  exact Measure.le_add_left le_rfl

/--
theorem `setToFun_add_measure` / 定理 `setToFun_add_measure`

English:
theorem setToFun_add_measure
  statement: {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C)
  proof: have hTμ_add : DominatedFinMeasAdditive (μ + ν) T (max C 0) :=
    (hTμ.of_le (le_max_left C 0)).add_measure_right μ ν (le_max_right C 0)
  have hTν_add : DominatedFinMeasAdditive (μ + ν) T' (max C' 0) :=
    (hTν.of_le (le_max_left C' 0)).add_measure_left μ ν (le_max_right C' 0)
  calc
    setToFun

中文:
定理 setToFun_add_measure
  结论: {ν : 测度 α} (hTμ : DominatedFinMeasAdditive μ T C)
  证明: have hTμ_add : DominatedFinMeasAdditive (μ + ν) T (max C 0) :=
    (hTμ.of_le (le_max_left C 0)).add_measure_right μ ν (le_max_right C 0)
  have hTν_add : DominatedFinMeasAdditive (μ + ν) T' (max C' 0) :=
    (hTν.of_le (le_max_left C' 0)).add_measure_left μ ν (le_max_right C' 0)
  calc
    setToFun

Depends on / 依赖: DominatedFinMeasAdditive, add_measure, add_measure_left, add_measure_right, le_max_left, le_max_right, of_le, setToFun, setToFun_add_left, setToFun_cong
-/
theorem setToFun_add_measure {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C)
    (hTν : DominatedFinMeasAdditive ν T' C') (hμ : Integrable f μ) (hν : Integrable f ν) :
    setToFun (μ + ν) (T + T') (hTμ.add_measure μ ν hTν) f =
      setToFun μ T hTμ f + setToFun ν T' hTν f :=
  have hTμ_add : DominatedFinMeasAdditive (μ + ν) T (max C 0) :=
    (hTμ.of_le (le_max_left C 0)).add_measure_right μ ν (le_max_right C 0)
  have hTν_add : DominatedFinMeasAdditive (μ + ν) T' (max C' 0) :=
    (hTν.of_le (le_max_left C' 0)).add_measure_left μ ν (le_max_right C' 0)
  calc
    setToFun (μ + ν) (T + T') (hTμ.add_measure μ ν hTν) f =
      setToFun (μ + ν) T hTμ_add f + setToFun (μ + ν) T' hTν_add f :=
        setToFun_add_left hTμ_add hTν_add f
    _ = setToFun μ T hTμ f + setToFun ν T' hTν f := by
      rw [setToFun_congr_measure_of_add_right hTμ_add hTμ f (hμ.add_measure hν)]; rw [setToFun_congr_measure_of_add_left hTν_add hTν f (hμ.add_measure hν)]

/--
theorem `setToFun_sub_measure` / 定理 `setToFun_sub_measure`

English:
theorem setToFun_sub_measure
  statement: {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C)
  proof: by
  simp [sub_eq_add_neg, setToFun_add_measure hTμ hTν.neg hμ hν, setToFun_neg' hTν]

中文:
定理 setToFun_sub_measure
  结论: {ν : 测度 α} (hTμ : DominatedFinMeasAdditive μ T C)
  证明: by
  simp [sub_eq_add_neg, setToFun_add_measure hTμ hTν.neg hμ hν, setToFun_neg' hTν]

Depends on / 依赖: setToFun_add_measure, setToFun_neg, sub_eq_add_neg
-/
theorem setToFun_sub_measure {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C)
    (hTν : DominatedFinMeasAdditive ν T' C') (hμ : Integrable f μ) (hν : Integrable f ν) :
    setToFun (μ + ν) (T - T') (hTμ.sub_measure μ ν hTν) f =
      setToFun μ T hTμ f - setToFun ν T' hTν f := by
  simp [sub_eq_add_neg, setToFun_add_measure hTμ hTν.neg hμ hν, setToFun_neg' hTν]

/--
theorem `setToFun_finsetSum_measure` / 定理 `setToFun_finsetSum_measure`

English:
theorem setToFun_finsetSum_measure
  statement: {ι} {s : Finset ι} (hs : s.Nonempty)
  proof: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | @cons i s his hs' ih =>
    simpa [his, ih fun j hj => hf j (Finset.mem_cons_of_mem hj)] using!
      setToFun_add_measure (hTs i) (DominatedFinMeasAdditive.finsetSum_measure hs' μ T C hTs)
      (hf i (Finset.me

中文:
定理 setToFun_finsetSum_measure
  结论: {ι} {s : 有限集 ι} (hs : s.非空)
  证明: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | @cons i s his hs' ih =>
    simpa [his, ih fun j hj => hf j (Finset.mem_cons_of_mem hj)] using!
      setToFun_add_measure (hTs i) (DominatedFinMeasAdditive.finsetSum_measure hs' μ T C hTs)
      (hf i (Finset.me

Depends on / 依赖: DominatedFinMeasAdditive, DominatedFinMeasAdditive.finsetSum_measure, Finset, Finset.Nonempty.cons_induction, Finset.mem_cons_of_mem, Finset.mem_cons_self, Nonempty, cons_induction, finsetSum_measure, integrable_finsetSum_measure, mem_cons_of_mem, mem_cons_self, setToFun_add_measure, singleton
-/
theorem setToFun_finsetSum_measure {ι} {s : Finset ι} (hs : s.Nonempty)
    {μ : ι -> Measure α} {T : ι -> Set α -> E ->L[Real] F} {C : ι -> Real}
    (hTs : forall i, DominatedFinMeasAdditive (μ i) (T i) (C i))
    (hf : forall i in s, Integrable f (μ i)) :
    setToFun (∑ i in s, μ i) (∑ i in s, T i)
      (DominatedFinMeasAdditive.finsetSum_measure hs μ T C hTs) f =
      ∑ i in s, setToFun (μ i) (T i) (hTs i) f := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | @cons i s his hs' ih =>
    simpa [his, ih fun j hj => hf j (Finset.mem_cons_of_mem hj)] using!
      setToFun_add_measure (hTs i) (DominatedFinMeasAdditive.finsetSum_measure hs' μ T C hTs)
      (hf i (Finset.mem_cons_self i s))
      (integrable_finsetSum_measure.2 fun j hj => hf j (Finset.mem_cons_of_mem hj))

/--
theorem `setToFun_top_smul_measure` / 定理 `setToFun_top_smul_measure`

English:
theorem setToFun_top_smul_measure
  given: (hT : DominatedFinMeasAdditive (∞ • μ) T C) (f : α -> E)
  proof: by
  refine setToFun_measure_zero' hT fun s _ hμs => ?_
  rw [lt_top_iff_ne_top] at hμs
  simp only [true_and, Measure.smul_apply, ENNReal.mul_eq_top,
    top_ne_zero, Ne, not_false_iff, not_or, Classical.not_not, smul_eq_mul] at hμs
  simp only [hμs.right, Measure.smul_apply, mul_zero, smul_eq_mul]

中文:
定理 setToFun_top_smul_measure
  条件: (hT : DominatedFinMeasAdditive (∞ • μ) T C) (f : α -> E)
  证明: by
  refine setToFun_measure_zero' hT fun s _ hμs => ?_
  rw [lt_top_iff_ne_top] at hμs
  simp only [true_and, Measure.smul_apply, ENNReal.mul_eq_top,
    top_ne_zero, Ne, not_false_iff, not_or, Classical.not_not, smul_eq_mul] at hμs
  simp only [hμs.right, Measure.smul_apply, mul_zero, smul_eq_mul]

Depends on / 依赖: Classical, Classical.not_not, ENNReal, ENNReal.mul_eq_top, GameAdd, Measure, Measure.smul_apply, Prod.GameAdd, Sym2.gameAdd_iff, WellFounded, WellFounded.fix, gameAdd_iff, hr.sym2_gameAdd.onFun, lt_top_iff_ne_top, mul_eq_top, mul_zero, not_false_iff, not_not, not_or, s.right
-/
theorem setToFun_top_smul_measure (hT : DominatedFinMeasAdditive (∞ • μ) T C) (f : α -> E) :
    setToFun (∞ • μ) T hT f = 0 := by
  refine setToFun_measure_zero' hT fun s _ hμs => ?_
  rw [lt_top_iff_ne_top] at hμs
  simp only [true_and, Measure.smul_apply, ENNReal.mul_eq_top,
    top_ne_zero, Ne, not_false_iff, not_or, Classical.not_not, smul_eq_mul] at hμs
  simp only [hμs.right, Measure.smul_apply, mul_zero, smul_eq_mul]

/--
theorem `setToFun_congr_smul_measure` / 定理 `setToFun_congr_smul_measure`

English:
theorem setToFun_congr_smul_measure
  statement: (c : Real>=0∞) (hc_ne_top : c != ∞)
  proof: by
  by_cases hc0 : c = 0
  · simp [hc0] at hT_smul
    have h : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0 := fun s hs _ => hT_smul.eq_zero hs
    rw [setToFun_zero_left' _ h]; rw [setToFun_measure_zero]
    simp [hc0]
  refine setToFun_congr_measure c⁻¹ c ?_ hc_ne_top (le_of_eq ?_) le_rfl hT 

中文:
定理 setToFun_congr_smul_measure
  结论: (c : 实数>=0∞) (hc_ne_top : c != ∞)
  证明: by
  by_cases hc0 : c = 0
  · simp [hc0] at hT_smul
    have h : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0 := fun s hs _ => hT_smul.eq_zero hs
    rw [setToFun_zero_left' _ h]; rw [setToFun_measure_zero]
    simp [hc0]
  refine setToFun_congr_measure c⁻¹ c ?_ hc_ne_top (le_of_eq ?_) le_rfl hT 

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, MeasurableSet, WellFounded, WellFounded.fix_eq, eq_zero, fix_eq, hT_smul, hT_smul.eq_zero, hc_ne_top, inv_mul_cancel, le_of_eq, le_rfl, one_smul, setToFun_congr_measure, setToFun_measure_zero, setToFun_zero_left, smul_smul
-/
theorem setToFun_congr_smul_measure (c : Real>=0∞) (hc_ne_top : c != ∞)
    (hT : DominatedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C')
    (f : α -> E) : setToFun μ T hT f = setToFun (c • μ) T hT_smul f := by
  by_cases hc0 : c = 0
  · simp [hc0] at hT_smul
    have h : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0 := fun s hs _ => hT_smul.eq_zero hs
    rw [setToFun_zero_left' _ h]; rw [setToFun_measure_zero]
    simp [hc0]
  refine setToFun_congr_measure c⁻¹ c ?_ hc_ne_top (le_of_eq ?_) le_rfl hT hT_smul f
  · simp [hc0]
  · rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc_ne_top, one_smul]

/--
theorem `setToFun_congr_smul_measure'` / 定理 `setToFun_congr_smul_measure'`

English:
theorem setToFun_congr_smul_measure'
  statement: (c : Real>=0)
  proof: by
  rw! [ENNReal.smul_def]
  apply setToFun_congr_smul_measure _ (by simp)

中文:
定理 setToFun_congr_smul_measure'
  结论: (c : 实数>=0)
  证明: by
  rw! [ENNReal.smul_def]
  apply setToFun_congr_smul_measure _ (by simp)

Depends on / 依赖: ENNReal, ENNReal.smul_def, GameAdd, GameAdd.recursion, recursion, setToFun_congr_smul_measure, smul_def
-/
theorem setToFun_congr_smul_measure' (c : Real>=0)
    (hT : DominatedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C')
    (f : α -> E) : setToFun μ T hT f = setToFun (c • μ) T hT_smul f := by
  rw! [ENNReal.smul_def]
  apply setToFun_congr_smul_measure _ (by simp)

/--
theorem `setToFun_add_left''` / 定理 `setToFun_add_left''`

English:
theorem setToFun_add_left''
  statement: {hT : DominatedFinMeasAdditive μ T C}
  proof: by
  have I : DominatedFinMeasAdditive (μ + μ') T C := .add_measure_right _ _ hT hC
  have A : setToFun (μ + μ') T I f = setToFun μ T hT f :=
    setToFun_congr_measure_of_add_right _ _ _ (hf.add_measure hf')
  have I' : DominatedFinMeasAdditive (μ + μ') T' C' := .add_measure_left _ _ hT' hC'
  have

中文:
定理 setToFun_add_left''
  结论: {hT : DominatedFinMeasAdditive μ T C}
  证明: by
  have I : DominatedFinMeasAdditive (μ + μ') T C := .add_measure_right _ _ hT hC
  have A : setToFun (μ + μ') T I f = setToFun μ T hT f :=
    setToFun_congr_measure_of_add_right _ _ _ (hf.add_measure hf')
  have I' : DominatedFinMeasAdditive (μ + μ') T' C' := .add_measure_left _ _ hT' hC'
  have

Depends on / 依赖: DominatedFinMeasAdditive, add_measure, add_measure_left, add_measure_right, hf.add_measure, of_measure_le, setToFun, setToFun_congr_measure_of_add_left, setToFun_congr_measure_of_add_right
-/
theorem setToFun_add_left'' {hT : DominatedFinMeasAdditive μ T C}
    {hT' : DominatedFinMeasAdditive μ' T' C'} {hT'' : DominatedFinMeasAdditive μ'' T'' C''}
    (h : forall s, MeasurableSet s -> (μ + μ') s < ∞ -> T'' s = T s + T' s)
    (hf : Integrable f μ) (hf' : Integrable f μ') (hμ : μ'' <= μ + μ')
    (hC : 0 <= C) (hC' : 0 <= C') (hC'' : 0 <= C'') :
    setToFun μ'' T'' hT'' f = setToFun μ T hT f + setToFun μ' T' hT' f := by
  have I : DominatedFinMeasAdditive (μ + μ') T C := .add_measure_right _ _ hT hC
  have A : setToFun (μ + μ') T I f = setToFun μ T hT f :=
    setToFun_congr_measure_of_add_right _ _ _ (hf.add_measure hf')
  have I' : DominatedFinMeasAdditive (μ + μ') T' C' := .add_measure_left _ _ hT' hC'
  have A' : setToFun (μ + μ') T' I' f = setToFun μ' T' hT' f :=
    setToFun_congr_measure_of_add_left _ _ _ (hf.add_measure hf')
  have I'' : DominatedFinMeasAdditive (μ + μ') T'' C'' := .of_measure_le hμ hT'' hC''
  have A'' : setToFun (μ + μ') T'' I'' f = setToFun μ'' T'' hT'' f := by
    apply setToFun_congr_measure_of_integrable (c' := 1) (by simp) (by simpa using hμ)
    apply hf.add_measure hf'
  rw [← A]; rw [← A']; rw [← A'']
  apply setToFun_add_left' _ _ _ h

/--
theorem `norm_setToFun_le_mul_norm` / 定理 `norm_setToFun_le_mul_norm`

English:
theorem norm_setToFun_le_mul_norm
  statement: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm hT hC f

中文:
定理 norm_setToFun_le_mul_norm
  结论: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm hT hC f

Depends on / 依赖: CompleteSpace, L1.norm_setToL1_le_mul_norm, L1.setToFun_eq_setToL1, norm_setToL1_le_mul_norm, norm_zero, reduceDIte, setToFun, setToFun_eq_setToL1
-/
theorem norm_setToFun_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E)
    (hC : 0 <= C) : ‖setToFun μ T hT f‖ <= C * ‖f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm hT hC f

/--
theorem `norm_setToFun_le_mul_norm'` / 定理 `norm_setToFun_le_mul_norm'`

English:
theorem norm_setToFun_le_mul_norm'
  given: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm' hT f

中文:
定理 norm_setToFun_le_mul_norm'
  条件: (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm' hT f

Depends on / 依赖: CompleteSpace, L1.norm_setToL1_le_mul_norm, L1.setToFun_eq_setToL1, norm_setToL1_le_mul_norm, norm_zero, reduceDIte, setToFun, setToFun_eq_setToL1
-/
theorem norm_setToFun_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) :
    ‖setToFun μ T hT f‖ <= max C 0 * ‖f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm' hT f

/--
theorem `norm_setToFun_le` / 定理 `norm_setToFun_le`

English:
theorem norm_setToFun_le
  given: (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) (hC : 0 <= C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm hT hC _

中文:
定理 norm_setToFun_le
  条件: (hT : DominatedFinMeasAdditive μ T C) (hf : 可积 f μ) (hC : 0 <= C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm hT hC _

Depends on / 依赖: CompleteSpace, L1.norm_setToL1_le_mul_norm, norm_setToL1_le_mul_norm, norm_zero, reduceDIte, setToFun, setToFun_eq
-/
theorem norm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) (hC : 0 <= C) :
    ‖setToFun μ T hT f‖ <= C * ‖hf.toL1 f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm hT hC _

/--
theorem `norm_setToFun_le'` / 定理 `norm_setToFun_le'`

English:
theorem norm_setToFun_le'
  given: (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm' hT _

中文:
定理 norm_setToFun_le'
  条件: (hT : DominatedFinMeasAdditive μ T C) (hf : 可积 f μ)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm' hT _

Depends on / 依赖: CompleteSpace, L1.norm_setToL1_le_mul_norm, norm_setToL1_le_mul_norm, norm_zero, reduceDIte, setToFun, setToFun_eq
-/
theorem norm_setToFun_le' (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    ‖setToFun μ T hT f‖ <= max C 0 * ‖hf.toL1 f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm' hT _

/--
theorem `enorm_setToFun_le` / 定理 `enorm_setToFun_le`

English:
theorem enorm_setToFun_le
  given: (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ; swap
  · simp [setToFun_undef _ hf]
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.mul_ne_top (by simp) hf.hasFiniteIntegral.ne)).1
  simp only [toReal_enorm, toReal_mul, coe_toReal, NNReal.coe

中文:
定理 enorm_setToFun_le
  条件: (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ; swap
  · simp [setToFun_undef _ hf]
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.mul_ne_top (by simp) hf.hasFiniteIntegral.ne)).1
  simp only [toReal_enorm, toReal_mul, coe_toReal, NNReal.coe

Depends on / 依赖: CompleteSpace, ENNReal, ENNReal.mul_ne_top, ENNReal.toReal_le_toReal, Integrable, Integrable.norm_toL1_eq_lintegral_enorm, NNReal, NNReal.coe_mk, coe_mk, coe_toReal, hasFiniteIntegral, hf.hasFiniteIntegral.ne, le_of_eq, mul_ne_top, norm_setToFun_le, norm_toL1_eq_lintegral_enorm, setToFun, setToFun_undef, toReal_enorm, toReal_le_toReal
-/
theorem enorm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) :
    ‖setToFun μ T hT f‖ₑ <= NNReal.mk C hC * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ; swap
  · simp [setToFun_undef _ hf]
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.mul_ne_top (by simp) hf.hasFiniteIntegral.ne)).1
  simp only [toReal_enorm, toReal_mul, coe_toReal, NNReal.coe_mk]
  apply (norm_setToFun_le hT hf hC).trans
  gcongr
  apply le_of_eq
  rw [Integrable.norm_toL1_eq_lintegral_enorm]

/--
theorem `norm_setToFun_le_toReal` / 定理 `norm_setToFun_le_toReal`

English:
theorem norm_setToFun_le_toReal
  given: (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  by_cases hf : Integrable f μ; swap
  · simp only [setToFun_undef _ hf, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  apply (norm_setToFun_le hT hf hC).

中文:
定理 norm_setToFun_le_to实数
  条件: (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  by_cases hf : Integrable f μ; swap
  · simp only [setToFun_undef _ hf, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  apply (norm_setToFun_le hT hf hC).

Depends on / 依赖: CompleteSpace, Integrable, Integrable.norm_toL1_eq_lintegral_enorm, NNReal, NNReal.coe_mk, coe_mk, norm_setToFun_le, norm_toL1_eq_lintegral_enorm, norm_zero, ofReal_norm, reduceDIte, setToFun, setToFun_undef
-/
theorem norm_setToFun_le_toReal (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) :
    ‖setToFun μ T hT f‖ <= NNReal.mk C hC * ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  by_cases hf : Integrable f μ; swap
  · simp only [setToFun_undef _ hf, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  apply (norm_setToFun_le hT hf hC).trans
  gcongr
  · simp
  rw [Integrable.norm_toL1_eq_lintegral_enorm]
  simp

/--
theorem `tendsto_setToFun_of_dominated_convergence` / 定理 `tendsto_setToFun_of_dominated_convergence`

English:
theorem tendsto_setToFun_of_dominated_convergence
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- `f` is a.e.-measurable, since it is the a.e.-pointwise limit of a.e.-measurable functions.
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ fs_measurable h_lim
  -- all functions we consid

中文:
定理 tendsto_setToFun_of_dominated_convergence
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- `f` is a.e.-measurable, since it is the a.e.-pointwise limit of a.e.-measurable functions.
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ fs_measurable h_lim
  -- all functions we consid

Depends on / 依赖: CompleteSpace, setToFun
-/
theorem tendsto_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C)
    {fs : Nat -> α -> E} {f : α -> E} (bound : α -> Real)
    (fs_measurable : forall n, AEStronglyMeasurable (fs n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : forall n, forallᵐ a ∂μ, ‖fs n a‖ <= bound a)
    (h_lim : forallᵐ a ∂μ, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) atTop (𝓝 <| setToFun μ T hT f) := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- `f` is a.e.-measurable, since it is the a.e.-pointwise limit of a.e.-measurable functions.
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ fs_measurable h_lim
  -- all functions we consider are integrable
  have fs_int : forall n, Integrable (fs n) μ := fun n =>
    bound_integrable.mono' (fs_measurable n) (h_bound _)
  have f_int : Integrable f μ :=
    ⟨f_measurable,
      hasFiniteIntegral_of_dominated_convergence bound_integrable.hasFiniteIntegral h_bound
        h_lim⟩
  -- it suffices to prove the result for the corresponding L1 functions
  suffices
    Tendsto (fun n => L1.setToL1 hT ((fs_int n).toL1 (fs n))) atTop
      (𝓝 (L1.setToL1 hT (f_int.toL1 f))) by
    convert! this with n
    · exact setToFun_eq hT (fs_int n)
    · exact setToFun_eq hT f_int
  -- the convergence of setToL1 follows from the convergence of the L1 functions
  refine L1.tendsto_setToL1 hT _ _ ?_
  -- up to some rewriting, what we need to prove is `h_lim`
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have lintegral_norm_tendsto_zero :
    Tendsto (fun n => ENNReal.toReal <| ∫⁻ a, ENNReal.ofReal ‖fs n a - f a‖ ∂μ) atTop (𝓝 0) :=
    (tendsto_toReal zero_ne_top).comp
      (tendsto_lintegral_norm_of_dominated_convergence fs_measurable
        bound_integrable.hasFiniteIntegral h_bound h_lim)
  convert! lintegral_norm_tendsto_zero with n
  rw [L1.norm_def]
  congr 1
  refine lintegral_congr_ae ?_
  rw [← Integrable.toL1_sub]
  refine ((fs_int n).sub f_int).coeFn_toL1.mono fun x hx => ?_
  dsimp only
  rw [hx]; rw [ofReal_norm]; rw [Pi.sub_apply]

/--
theorem `tendsto_setToFun_filter_of_dominated_convergence` / 定理 `tendsto_setToFun_filter_of_dominated_convergence`

English:
theorem tendsto_setToFun_filter_of_dominated_convergence
  statement: (hT : DominatedFinMeasAdditive μ T C) {ι}
  proof: by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl : forall s in l, exists a, forall b >= a, x b in s := by rwa [tendsto_atTop'] at xl
  have h :
    { x : ι | (fun n => AEStronglyMeasurable (fs n) μ) x } inter
        { x : ι | (fun n => forallᵐ a ∂μ, ‖fs n a‖ <= bound a) x } in l :=
    int

中文:
定理 tendsto_setToFun_filter_of_dominated_convergence
  结论: (hT : DominatedFinMeasAdditive μ T C) {ι}
  证明: by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl : forall s in l, exists a, forall b >= a, x b in s := by rwa [tendsto_atTop'] at xl
  have h :
    { x : ι | (fun n => AEStronglyMeasurable (fs n) μ) x } inter
        { x : ι | (fun n => forallᵐ a ∂μ, ‖fs n a‖ <= bound a) x } in l :=
    int

Depends on / 依赖: AEStronglyMeasurable, bound_integrable, h_bound, hfs_meas, inter_mem, self_le_add_left, tendsto_add_atTop_iff_nat, tendsto_atTop, tendsto_iff_seq_tendsto, tendsto_setToFun_of_dominated_convergence
-/
theorem tendsto_setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {ι}
    {l : Filter ι} [l.IsCountablyGenerated] {fs : ι -> α -> E} {f : α -> E} (bound : α -> Real)
    (hfs_meas : forallᶠ n in l, AEStronglyMeasurable (fs n) μ)
    (h_bound : forallᶠ n in l, forallᵐ a ∂μ, ‖fs n a‖ <= bound a) (bound_integrable : Integrable bound μ)
    (h_lim : forallᵐ a ∂μ, Tendsto (fun n => fs n a) l (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) l (𝓝 <| setToFun μ T hT f) := by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl : forall s in l, exists a, forall b >= a, x b in s := by rwa [tendsto_atTop'] at xl
  have h :
    { x : ι | (fun n => AEStronglyMeasurable (fs n) μ) x } inter
        { x : ι | (fun n => forallᵐ a ∂μ, ‖fs n a‖ <= bound a) x } in l :=
    inter_mem hfs_meas h_bound
  obtain ⟨k, h⟩ := hxl _ h
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_setToFun_of_dominated_convergence hT bound ?_ bound_integrable ?_ ?_
  · exact fun n => (h _ (self_le_add_left _ _)).1
  · exact fun n => (h _ (self_le_add_left _ _)).2
  · filter_upwards [h_lim]
    refine fun a h_lin => @Tendsto.comp _ _ _ (fun n => x (n + k)) (fun n => fs n a) _ _ _ h_lin ?_
    rwa [tendsto_add_atTop_iff_nat]

/--
theorem `hasSum_setToFun_of_dominated_convergence` / 定理 `hasSum_setToFun_of_dominated_convergence`

English:
theorem hasSum_setToFun_of_dominated_convergence
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  have hb_nonneg : forallᵐ a ∂μ, forall n, 0 <= bound n a :=
    eventually_countable_forall.2 fun n => (h_bound n).mono fun a => (norm_nonneg _).trans
  have hb_le_tsum : forall n, bound n <=ᵐ[μ] fun a => ∑' n, bound n a := by
    intro n
    filter_upwards [hb_nonneg, bound_summable]
      with

中文:
定理 hasSum_setToFun_of_dominated_convergence
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  have hb_nonneg : forallᵐ a ∂μ, forall n, 0 <= bound n a :=
    eventually_countable_forall.2 fun n => (h_bound n).mono fun a => (norm_nonneg _).trans
  have hb_le_tsum : forall n, bound n <=ᵐ[μ] fun a => ∑' n, bound n a := by
    intro n
    filter_upwards [hb_nonneg, bound_summable]
      with

Depends on / 依赖: EventuallyLE, EventuallyLE.trans, Integrable, bound_integrable, bound_integrable.mono, bound_summable, eventually_countable_forall, filter_upwards, hF_integrable, hF_meas, h_bound, ha_sum, ha_sum.le_tsum, hb_le_tsum, hb_nonneg, le_tsum, norm_nonneg
-/
theorem hasSum_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C)
    {ι} [Countable ι] {F : ι -> α -> E} {f : α -> E}
    (bound : ι -> α -> Real) (hF_meas : forall n, AEStronglyMeasurable (F n) μ)
    (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound n a)
    (bound_summable : forallᵐ a ∂μ, Summable fun n => bound n a)
    (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ)
    (h_lim : forallᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => setToFun μ T hT (F n)) (setToFun μ T hT f) := by
  have hb_nonneg : forallᵐ a ∂μ, forall n, 0 <= bound n a :=
    eventually_countable_forall.2 fun n => (h_bound n).mono fun a => (norm_nonneg _).trans
  have hb_le_tsum : forall n, bound n <=ᵐ[μ] fun a => ∑' n, bound n a := by
    intro n
    filter_upwards [hb_nonneg, bound_summable]
      with _ ha0 ha_sum using ha_sum.le_tsum _ fun i _ => ha0 i
  have hF_integrable : forall n, Integrable (F n) μ := by
    refine fun n => bound_integrable.mono' (hF_meas n) ?_
    exact EventuallyLE.trans (h_bound n) (hb_le_tsum n)
  simp only [HasSum, ← setToFun_finsetSum _ _ fun n _ => hF_integrable n]
  refine tendsto_setToFun_filter_of_dominated_convergence _
      (fun a => ∑' n, bound n a) ?_ ?_ bound_integrable h_lim
  · exact Eventually.of_forall fun s => s.aestronglyMeasurable_fun_sum fun n _ => hF_meas n
  · filter_upwards with s
    filter_upwards [eventually_countable_forall.2 h_bound, hb_nonneg, bound_summable]
      with a hFa ha0 has
    calc
      ‖∑ n in s, F n a‖ <= ∑ n in s, bound n a := norm_sum_le_of_le _ fun n _ => hFa n
      _ <= ∑' n, bound n a := has.sum_le_tsum _ (fun n _ => ha0 n)

/--
theorem `setToFun_tsum` / 定理 `setToFun_tsum`

English:
theorem setToFun_tsum
  statement: [CompleteSpace E] (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hf'' i : AEMeasurable (‖f i ·‖ₑ) μ := (hf i).enorm
  have hhh : forallᵐ a : α ∂μ, Summable fun n => (‖f n a‖₊ : Real) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.tsum hf'') hf').mono ?_
    i

中文:
定理 setToFun_tsum
  结论: [完备空间 E] (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hf'' i : AEMeasurable (‖f i ·‖ₑ) μ := (hf i).enorm
  have hhh : forallᵐ a : α ∂μ, Summable fun n => (‖f n a‖₊ : Real) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.tsum hf'') hf').mono ?_
    i

Depends on / 依赖: AEMeasurable, AEMeasurable.tsum, CompleteSpace, ENNReal, ENNReal.tsum_coe_ne_top_iff_summable_coe, MeasureTheory, MeasureTheory.hasSum_setToFun_of_dominated_convergence, Summable, ae_lt_top, convert, filter_upwards, hasSum_setToFun_of_dominated_convergence, hx.ne, lintegral_tsum, setToFun, tsum_coe_ne_top_iff_summable_coe, tsum_eq, tsum_eq.symm
-/
theorem setToFun_tsum [CompleteSpace E] (hT : DominatedFinMeasAdditive μ T C)
    {ι} [Countable ι] {f : ι -> α -> E} (hf : forall i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ != ∞) :
    setToFun μ T hT (fun a => ∑' i, f i a) = ∑' i, setToFun μ T hT (f i) := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hf'' i : AEMeasurable (‖f i ·‖ₑ) μ := (hf i).enorm
  have hhh : forallᵐ a : α ∂μ, Summable fun n => (‖f n a‖₊ : Real) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.tsum hf'') hf').mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  convert!
    (MeasureTheory.hasSum_setToFun_of_dominated_convergence hT (fun i a => ‖f i a‖₊) hf _ hhh ⟨_, _⟩
        _).tsum_eq.symm
  · intro n
    filter_upwards with x
    rfl
  · fun_prop
  · dsimp [HasFiniteIntegral]
    have : ∫⁻ a, ∑' n, ‖f n a‖ₑ ∂μ < ⊤ := by rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
    convert! this using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm, NNReal.nnnorm_eq]
    filter_upwards [hhh] with a ha
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp ha)
  · filter_upwards [hhh] with x hx
    exact hx.of_norm.hasSum

/--
theorem `tendsto_setToFun_filter_of_norm_le_const` / 定理 `tendsto_setToFun_filter_of_norm_le_const`

English:
theorem tendsto_setToFun_filter_of_norm_le_const
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: by
  obtain ⟨c, h_boundc⟩ := h_bound
  let C : α -> Real := (fun _ => c)
  exact tendsto_setToFun_filter_of_dominated_convergence hT
    C h_meas h_boundc (integrable_const c) h_lim

omit [NormedSpace Real E] in

中文:
定理 tendsto_setToFun_filter_of_norm_le_const
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: by
  obtain ⟨c, h_boundc⟩ := h_bound
  let C : α -> Real := (fun _ => c)
  exact tendsto_setToFun_filter_of_dominated_convergence hT
    C h_meas h_boundc (integrable_const c) h_lim

omit [NormedSpace Real E] in

Depends on / 依赖: h_bound, h_boundc, h_lim, h_meas, integrable_const, tendsto_setToFun_filter_of_dominated_convergence
-/
theorem tendsto_setToFun_filter_of_norm_le_const (hT : DominatedFinMeasAdditive μ T C)
    {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι -> α -> E} [IsFiniteMeasure μ] {f : α -> E}
    (h_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : exists C, forallᶠ n in l, forallᵐ ω ∂μ, ‖F n ω‖ <= C)
    (h_lim : forallᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f ω))) :
    Tendsto (fun n => setToFun μ T hT (F n)) l (𝓝 (setToFun μ T hT f)) := by
  obtain ⟨c, h_boundc⟩ := h_bound
  let C : α -> Real := (fun _ => c)
  exact tendsto_setToFun_filter_of_dominated_convergence hT
    C h_meas h_boundc (integrable_const c) h_lim

omit [NormedSpace Real E] in
/--
theorem `_root_.measurableSet_integrable` / 定理 `_root_.measurableSet_integrable`

English:
theorem _root_.measurableSet_integrable
  statement: {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
  proof: by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_prod_right hf.enorm) measurable_const

中文:
定理 _root_.measurableSet_integrable
  结论: {β : 类型} {mβ : 可测空间 β} [SFinite μ]
  证明: by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_prod_right hf.enorm) measurable_const

Depends on / 依赖: Integrable, Measurable, Measurable.lintegral_prod_right, aestronglyMeasurable, hf.enorm, hf.of_uncurry_left.aestronglyMeasurable, lintegral_prod_right, measurableSet_lt, measurable_const, of_uncurry_left, simp_rw, true_and
-/
theorem _root_.measurableSet_integrable {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    ⦃f : β -> α -> E⦄ (hf : StronglyMeasurable (Function.uncurry f)) :
    MeasurableSet {x | Integrable (f x) μ} := by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_prod_right hf.enorm) measurable_const

/--
theorem `StronglyMeasurable.setToFun_prod_right` / 定理 `StronglyMeasurable.setToFun_prod_right`

English:
theorem StronglyMeasurable.setToFun_prod_right
  statement: {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
  proof: by
  classical
  by_cases hF : CompleteSpace F; swap;
  · simp [setToFun, hF, stronglyMeasurable_const]
  borelize E
  have : SeparableSpace (range (Function.uncurry f) union {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : Nat -> SimpleFunc (β × α) E :=
    SimpleFunc.approxOn 

中文:
定理 StronglyMeasurable.setToFun_prod_right
  结论: {β : 类型} {mβ : 可测空间 β} [SFinite μ]
  证明: by
  classical
  by_cases hF : CompleteSpace F; swap;
  · simp [setToFun, hF, stronglyMeasurable_const]
  borelize E
  have : SeparableSpace (range (Function.uncurry f) union {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : Nat -> SimpleFunc (β × α) E :=
    SimpleFunc.approxOn 

Depends on / 依赖: CompleteSpace, Function, Function.uncurry, Integrable, Prod.mk, SeparableSpace, SimpleFunc, SimpleFunc.approxOn, approxOn, borelize, classical, hf.measurable, hf.separableSpace_range_union_singleton, measurable, measurable_prodMk_left, separableSpace_range_union_singleton, setToFun, stronglyMeasurable_const, uncurry
-/
theorem StronglyMeasurable.setToFun_prod_right {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    (hT : DominatedFinMeasAdditive μ T C)
    (h'T : forall (s : Set (β × α)), MeasurableSet s -> StronglyMeasurable fun x => T (Prod.mk x ⁻¹' s))
    ⦃f : β -> α -> E⦄ (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable fun x => setToFun μ T hT (f x) := by
  classical
  by_cases hF : CompleteSpace F; swap;
  · simp [setToFun, hF, stronglyMeasurable_const]
  borelize E
  have : SeparableSpace (range (Function.uncurry f) union {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : Nat -> SimpleFunc (β × α) E :=
    SimpleFunc.approxOn _ hf.measurable (range (Function.uncurry f) union {0}) 0 (by simp)
  let s' : Nat -> β -> SimpleFunc α E := fun n x => (s n).comp (Prod.mk x) measurable_prodMk_left
  let f' : Nat -> β -> F := fun n =>
    {x | Integrable (f x) μ}.indicator fun x => (s' n x).setToSimpleFunc T
  have hf' n : StronglyMeasurable (f' n) := by
    refine StronglyMeasurable.indicator ?_ (measurableSet_integrable hf)
    have : forall x, ((s' n x).range.filter fun x => x != 0) subseteq (s n).range := by
      intro x; refine Finset.Subset.trans (Finset.filter_subset _ _) ?_; intro y
      simp_rw [SimpleFunc.mem_range]; rintro ⟨z, rfl⟩; exact ⟨(x, z), rfl⟩
    simp_rw [SimpleFunc.setToSimpleFunc_eq_sum_of_subset T hT.1.map_empty_eq_zero (this _)]
    refine Finset.stronglyMeasurable_fun_sum _ fun x _ => ?_
    simp only [s', SimpleFunc.coe_comp, preimage_comp]
    apply StronglyMeasurable.apply_continuousLinearMap
    apply h'T
    exact (s n).measurableSet_fiber x
  have h2f' : Tendsto f' atTop (𝓝 fun x : β => setToFun μ T hT (f x)) := by
    apply tendsto_pi_nhds.2 fun x => ?_
    by_cases hfx : Integrable (f x) μ
    · have (n : _) : Integrable (s' n x) μ := by
        apply (hfx.norm.add hfx.norm).mono' (s' n x).aestronglyMeasurable
        filter_upwards with y
        simp_rw [s', SimpleFunc.coe_comp]; exact SimpleFunc.norm_approxOn_zero_le _ _ (x, y) n
      simp only [mem_ofPred_eq, hfx, indicator_of_mem, this,
        ← setToFun_simpleFunc_eq_setToSimpleFunc hT, f']
      refine
        tendsto_setToFun_of_dominated_convergence hT (fun y => ‖f x y‖ + ‖f x y‖)
          (fun n => (s' n x).aestronglyMeasurable) (hfx.norm.add hfx.norm) ?_ ?_
      · refine fun n => Eventually.of_forall fun y =>
          SimpleFunc.norm_approxOn_zero_le ?_ ?_ (x, y) n
        · exact hf.measurable
        · simp
      · refine Eventually.of_forall fun y => SimpleFunc.tendsto_approxOn ?_ ?_ ?_
        · exact hf.measurable.of_uncurry_left
        · simp
        apply subset_closure
        simp [-Function.uncurry_apply_pair]
    · simp [f', hfx, setToFun_undef]
  exact stronglyMeasurable_of_tendsto _ hf' h2f'

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

/--
theorem `continuousWithinAt_setToFun_of_dominated` / 定理 `continuousWithinAt_setToFun_of_dominated`

English:
theorem continuousWithinAt_setToFun_of_dominated
  statement: (hT : DominatedFinMeasAdditive μ T C)
  proof: tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

中文:
定理 continuousWithinAt_setToFun_of_dominated
  结论: (hT : DominatedFinMeasAdditive μ T C)
  证明: tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

Depends on / 依赖: tendsto_setToFun_filter_of_dominated_convergence
-/
theorem continuousWithinAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C)
    {fs : X -> α -> E} {x₀ : X} {bound : α -> Real} {s : Set X}
    (hfs_meas : forallᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (fs x) μ)
    (h_bound : forallᶠ x in 𝓝[s] x₀, forallᵐ a ∂μ, ‖fs x a‖ <= bound a) (bound_integrable : Integrable bound μ)
    (h_cont : forallᵐ a ∂μ, ContinuousWithinAt (fun x => fs x a) s x₀) :
    ContinuousWithinAt (fun x => setToFun μ T hT (fs x)) s x₀ :=
  tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

/--
theorem `continuousAt_setToFun_of_dominated` / 定理 `continuousAt_setToFun_of_dominated`

English:
theorem continuousAt_setToFun_of_dominated
  statement: (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E}
  proof: tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

中文:
定理 continuousAt_setToFun_of_dominated
  结论: (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E}
  证明: tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

Depends on / 依赖: tendsto_setToFun_filter_of_dominated_convergence
-/
theorem continuousAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E}
    {x₀ : X} {bound : α -> Real} (hfs_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (fs x) μ)
    (h_bound : forallᶠ x in 𝓝 x₀, forallᵐ a ∂μ, ‖fs x a‖ <= bound a) (bound_integrable : Integrable bound μ)
    (h_cont : forallᵐ a ∂μ, ContinuousAt (fun x => fs x a) x₀) :
    ContinuousAt (fun x => setToFun μ T hT (fs x)) x₀ :=
  tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

/--
theorem `continuousOn_setToFun_of_dominated` / 定理 `continuousOn_setToFun_of_dominated`

English:
theorem continuousOn_setToFun_of_dominated
  statement: (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E}
  proof: by
  intro x hx
  refine continuousWithinAt_setToFun_of_dominated hT ?_ ?_ bound_integrable ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx using hfs_meas x hx
  · filter_upwards [self_mem_nhdsWithin] with x hx using h_bound x hx
  · filter_upwards [h_cont] with a ha using ha x hx

中文:
定理 continuousOn_setToFun_of_dominated
  结论: (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E}
  证明: by
  intro x hx
  refine continuousWithinAt_setToFun_of_dominated hT ?_ ?_ bound_integrable ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx using hfs_meas x hx
  · filter_upwards [self_mem_nhdsWithin] with x hx using h_bound x hx
  · filter_upwards [h_cont] with a ha using ha x hx

Depends on / 依赖: bound_integrable, continuousWithinAt_setToFun_of_dominated, filter_upwards, h_bound, h_cont, hfs_meas, self_mem_nhdsWithin
-/
theorem continuousOn_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E}
    {bound : α -> Real} {s : Set X} (hfs_meas : forall x in s, AEStronglyMeasurable (fs x) μ)
    (h_bound : forall x in s, forallᵐ a ∂μ, ‖fs x a‖ <= bound a) (bound_integrable : Integrable bound μ)
    (h_cont : forallᵐ a ∂μ, ContinuousOn (fun x => fs x a) s) :
    ContinuousOn (fun x => setToFun μ T hT (fs x)) s := by
  intro x hx
  refine continuousWithinAt_setToFun_of_dominated hT ?_ ?_ bound_integrable ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx using hfs_meas x hx
  · filter_upwards [self_mem_nhdsWithin] with x hx using h_bound x hx
  · filter_upwards [h_cont] with a ha using ha x hx

/--
theorem `continuous_setToFun_of_dominated` / 定理 `continuous_setToFun_of_dominated`

English:
theorem continuous_setToFun_of_dominated
  statement: (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E}
  proof: continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_setToFun_of_dominated hT (Eventually.of_forall hfs_meas)
(Eventually.of_forall h_bound) ‹_›
      h_cont.mono fun _ => Continuous.continuousAt

中文:
定理 continuous_setToFun_of_dominated
  结论: (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E}
  证明: continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_setToFun_of_dominated hT (Eventually.of_forall hfs_meas)
(Eventually.of_forall h_bound) ‹_›
      h_cont.mono fun _ => Continuous.continuousAt

Depends on / 依赖: Continuous, Continuous.continuousAt, Eventually, Eventually.of_forall, continuousAt, continuousAt_setToFun_of_dominated, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, h_bound, h_cont, h_cont.mono, hfs_meas, of_forall
-/
theorem continuous_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E}
    {bound : α -> Real} (hfs_meas : forall x, AEStronglyMeasurable (fs x) μ)
    (h_bound : forall x, forallᵐ a ∂μ, ‖fs x a‖ <= bound a) (bound_integrable : Integrable bound μ)
    (h_cont : forallᵐ a ∂μ, Continuous fun x => fs x a) : Continuous fun x => setToFun μ T hT (fs x) :=
  continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_setToFun_of_dominated hT (Eventually.of_forall hfs_meas)
(Eventually.of_forall h_bound) ‹_›
      h_cont.mono fun _ => Continuous.continuousAt

end Function

end MeasureTheory
