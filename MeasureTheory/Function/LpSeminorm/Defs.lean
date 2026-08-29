/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# ℒp space

This file describes properties of almost everywhere strongly measurable functions with finite
`p`-seminorm, denoted by `eLpNorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`,
`(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and `essSup ‖f‖ μ` for `p=∞`.

The Prop-valued `MemLp f p μ` states that a function `f : α → E` has finite `p`-seminorm
and is almost everywhere strongly measurable.

## Main definitions

* `eLpNorm' f p μ` : `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a measurable
  space and `F` is a normed group.
* `eLpNormEssSup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `essSup ‖f‖ μ`.
* `eLpNorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `eLpNorm' f p μ`
  for `0 < p < ∞` and to `eLpNormEssSup f μ` for `p = ∞`.

* `MemLp f p μ` : property that the function `f` is almost everywhere strongly measurable and has
  finite `p`-seminorm for the measure `μ` (`eLpNorm f p μ < ∞`)

-/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : Real>=0∞} {q : Real} {f : α -> E}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

/-!
### ℒp seminorm

We define the ℒp seminorm, denoted by `eLpNorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `eLpNorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `eLpNormEssSup f μ`).

We also define a predicate `MemLp f p μ`, requesting that a function is almost everywhere
measurable and has finite `eLpNorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `eLpNorm'` and `eLpNormEssSup` when it makes sense,
deduce it for `eLpNorm`, and translate it in terms of `MemLp`.
-/


/--
Definition of `eLpNorm'` / `eLpNorm'` 的定义

English:
definition eLpNorm'
  signature: {_ : MeasurableSpace α} (f : α -> ε) (q : Real) (μ : Measure α)
  body: (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q)

中文:
定义 eLpNorm'
  签名: {_ : 可测空间 α} (f : α -> ε) (q : 实数) (μ : 测度 α)
  定义体: (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q)
-/
def eLpNorm' {_ : MeasurableSpace α} (f : α -> ε) (q : Real) (μ : Measure α) : Real>=0∞ :=
  (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q)

/--
lemma `eLpNorm'_eq_lintegral_enorm` / 引理 `eLpNorm'_eq_lintegral_enorm`

English:
lemma eLpNorm'_eq_lintegral_enorm
  given: (f : α -> ε) (q : Real) (μ : Measure α)
  proof: rfl

中文:
引理 eLpNorm'_eq_lintegral_enorm
  条件: (f : α -> ε) (q : 实数) (μ : 测度 α)
  证明: rfl
-/
lemma eLpNorm'_eq_lintegral_enorm (f : α -> ε) (q : Real) (μ : Measure α) :
    eLpNorm' f q μ = (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q) :=
  rfl

/--
Definition of `eLpNormEssSup` / `eLpNormEssSup` 的定义

English:
definition eLpNormEssSup
  signature: (f : α -> ε) (μ : Measure α)
  body: essSup (fun x => ‖f x‖ₑ) μ

中文:
定义 eLpNormEssSup
  签名: (f : α -> ε) (μ : 测度 α)
  定义体: essSup (fun x => ‖f x‖ₑ) μ

Depends on / 依赖: essSup
-/
def eLpNormEssSup (f : α -> ε) (μ : Measure α) :=
  essSup (fun x => ‖f x‖ₑ) μ

/--
lemma `eLpNormEssSup_eq_essSup_enorm` / 引理 `eLpNormEssSup_eq_essSup_enorm`

English:
lemma eLpNormEssSup_eq_essSup_enorm
  given: (f : α -> ε) (μ : Measure α)
  proof: rfl

中文:
引理 eLpNormEssSup_eq_essSup_enorm
  条件: (f : α -> ε) (μ : 测度 α)
  证明: rfl
-/
lemma eLpNormEssSup_eq_essSup_enorm (f : α -> ε) (μ : Measure α) :
    eLpNormEssSup f μ = essSup (‖f ·‖ₑ) μ := rfl

/--
Definition of `eLpNorm` / `eLpNorm` 的定义

English:
definition eLpNorm
  signature: {_ : MeasurableSpace α}
  body: if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f (ENNReal.toReal p) μ

中文:
定义 eLpNorm
  签名: {_ : 可测空间 α}
  定义体: if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f (ENNReal.toReal p) μ

Depends on / 依赖: ENNReal, ENNReal.toReal, eLpNorm, eLpNormEssSup, toReal, volume_tac
-/
def eLpNorm {_ : MeasurableSpace α}
    (f : α -> ε) (p : Real>=0∞) (μ : Measure α := by volume_tac) : Real>=0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f (ENNReal.toReal p) μ

variable {μ ν : Measure α}

/--
theorem `eLpNorm_eq_eLpNorm'` / 定理 `eLpNorm_eq_eLpNorm'`

English:
theorem eLpNorm_eq_eLpNorm'
  given: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε}
  proof: by simp [eLpNorm, hp_ne_zero, hp_ne_top]

中文:
定理 eLpNorm_eq_eLpNorm'
  条件: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε}
  证明: by simp [eLpNorm, hp_ne_zero, hp_ne_top]

Depends on / 依赖: eLpNorm, hp_ne_top, hp_ne_zero
-/
theorem eLpNorm_eq_eLpNorm' (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} :
    eLpNorm f p μ = eLpNorm' f (ENNReal.toReal p) μ := by simp [eLpNorm, hp_ne_zero, hp_ne_top]

/--
lemma `eLpNorm_nnreal_eq_eLpNorm'` / 引理 `eLpNorm_nnreal_eq_eLpNorm'`

English:
lemma eLpNorm_nnreal_eq_eLpNorm'
  given: {f : α -> ε} {p : Real>=0} (hp : p != 0)
  proof: eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top

中文:
引理 eLpNorm_nnreal_eq_eLpNorm'
  条件: {f : α -> ε} {p : 实数>=0} (hp : p != 0)
  证明: eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, coe_ne_top, eLpNorm_eq_eLpNorm
-/
lemma eLpNorm_nnreal_eq_eLpNorm' {f : α -> ε} {p : Real>=0} (hp : p != 0) :
    eLpNorm f p μ = eLpNorm' f p μ :=
  eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top

/--
lemma `eLpNorm_eq_lintegral_rpow_enorm_toReal` / 引理 `eLpNorm_eq_lintegral_rpow_enorm_toReal`

English:
lemma eLpNorm_eq_lintegral_rpow_enorm_toReal
  given: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε}
  proof: by
  rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]; rw [eLpNorm'_eq_lintegral_enorm]

@[deprecated (since := "2026-02-09")]
alias eLpNorm_eq_lintegral_rpow_enorm := eLpNorm_eq_lintegral_rpow_enorm_toReal

中文:
引理 eLpNorm_eq_lintegral_rpow_enorm_to实数
  条件: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε}
  证明: by
  rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]; rw [eLpNorm'_eq_lintegral_enorm]

@[deprecated (since := "2026-02-09")]
alias eLpNorm_eq_lintegral_rpow_enorm := eLpNorm_eq_lintegral_rpow_enorm_toReal

Depends on / 依赖: _eq_lintegral_enorm, eLpNorm, eLpNorm_eq_eLpNorm, hp_ne_top, hp_ne_zero
-/
lemma eLpNorm_eq_lintegral_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} :
    eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]; rw [eLpNorm'_eq_lintegral_enorm]

@[deprecated (since := "2026-02-09")]
alias eLpNorm_eq_lintegral_rpow_enorm := eLpNorm_eq_lintegral_rpow_enorm_toReal

/--
lemma `eLpNorm_nnreal_eq_lintegral` / 引理 `eLpNorm_nnreal_eq_lintegral`

English:
lemma eLpNorm_nnreal_eq_lintegral
  given: {f : α -> ε} {p : Real>=0} (hp : p != 0)
  proof: eLpNorm_nnreal_eq_eLpNorm' hp

中文:
引理 eLpNorm_nnreal_eq_lintegral
  条件: {f : α -> ε} {p : 实数>=0} (hp : p != 0)
  证明: eLpNorm_nnreal_eq_eLpNorm' hp

Depends on / 依赖: eLpNorm_nnreal_eq_eLpNorm
-/
lemma eLpNorm_nnreal_eq_lintegral {f : α -> ε} {p : Real>=0} (hp : p != 0) :
    eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ (p : Real) ∂μ) ^ (1 / (p : Real)) :=
  eLpNorm_nnreal_eq_eLpNorm' hp

/--
theorem `eLpNorm_one_eq_lintegral_enorm` / 定理 `eLpNorm_one_eq_lintegral_enorm`

English:
theorem eLpNorm_one_eq_lintegral_enorm
  given: {f : α -> ε}
  statement: eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
  proof: by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal one_ne_zero ENNReal.coe_ne_top,
    ENNReal.toReal_one, one_div_one, ENNReal.rpow_one]

@[simp]

中文:
定理 eLpNorm_one_eq_lintegral_enorm
  条件: {f : α -> ε}
  结论: eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
  证明: by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal one_ne_zero ENNReal.coe_ne_top,
    ENNReal.toReal_one, one_div_one, ENNReal.rpow_one]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.rpow_one, ENNReal.toReal_one, coe_ne_top, eLpNorm_eq_lintegral_rpow_enorm_toReal, one_div_one, one_ne_zero, rpow_one, simp_rw, toReal_one
-/
theorem eLpNorm_one_eq_lintegral_enorm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal one_ne_zero ENNReal.coe_ne_top,
    ENNReal.toReal_one, one_div_one, ENNReal.rpow_one]

@[simp]
/--
theorem `eLpNorm_exponent_top` / 定理 `eLpNorm_exponent_top`

English:
theorem eLpNorm_exponent_top
  given: {f : α -> ε}
  statement: eLpNorm f ∞ μ = eLpNormEssSup f μ
  proof: by simp [eLpNorm]

中文:
定理 eLpNorm_exponent_top
  条件: {f : α -> ε}
  结论: eLpNorm f ∞ μ = eLpNormEssSup f μ
  证明: by simp [eLpNorm]

Depends on / 依赖: eLpNorm
-/
theorem eLpNorm_exponent_top {f : α -> ε} : eLpNorm f ∞ μ = eLpNormEssSup f μ := by simp [eLpNorm]

/--
Definition of `MemLp` / `MemLp` 的定义

English:
definition MemLp
  signature: [TopologicalSpace ε] (f : α -> ε) (p : Real>=0∞) (μ : Measure α := by volume_tac)
  body: AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞

中文:
定义 MemLp
  签名: [拓扑空间 ε] (f : α -> ε) (p : 实数>=0∞) (μ : 测度 α := by volume_tac)
  定义体: AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞

Depends on / 依赖: AEStronglyMeasurable, eLpNorm, volume_tac
-/
def MemLp [TopologicalSpace ε] (f : α -> ε) (p : Real>=0∞) (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞

/--
theorem `MemLp.aestronglyMeasurable` / 定理 `MemLp.aestronglyMeasurable`

English:
theorem MemLp.aestronglyMeasurable
  given: [TopologicalSpace ε] {f : α -> ε} {p : Real>=0∞} (h : MemLp f p μ)
  proof: h.1

中文:
定理 MemLp.aestronglyMeasurable
  条件: [拓扑空间 ε] {f : α -> ε} {p : 实数>=0∞} (h : MemLp f p μ)
  证明: h.1
-/
theorem MemLp.aestronglyMeasurable [TopologicalSpace ε] {f : α -> ε} {p : Real>=0∞} (h : MemLp f p μ) :
    AEStronglyMeasurable f μ :=
  h.1

/--
lemma `MemLp.aemeasurable` / 引理 `MemLp.aemeasurable`

English:
lemma MemLp.aemeasurable
  statement: [MeasurableSpace ε] [TopologicalSpace ε]
  proof: hf.aestronglyMeasurable.aemeasurable

中文:
引理 MemLp.aemeasurable
  结论: [可测空间 ε] [拓扑空间 ε]
  证明: hf.aestronglyMeasurable.aemeasurable

Depends on / 依赖: aemeasurable, aestronglyMeasurable, hf.aestronglyMeasurable.aemeasurable
-/
lemma MemLp.aemeasurable [MeasurableSpace ε] [TopologicalSpace ε]
    [TopologicalSpace.PseudoMetrizableSpace ε] [BorelSpace ε]
    {f : α -> ε} {p : Real>=0∞} (hf : MemLp f p μ) :
    AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

/--
theorem `lintegral_rpow_enorm_eq_rpow_eLpNorm'` / 定理 `lintegral_rpow_enorm_eq_rpow_eLpNorm'`

English:
theorem lintegral_rpow_enorm_eq_rpow_eLpNorm'
  given: {f : α -> ε} (hq0_lt : 0 < q)
  proof: by
  rw [eLpNorm'_eq_lintegral_enorm]; rw [← ENNReal.rpow_mul]; rw [one_div]; rw [inv_mul_cancel₀]; rw [ENNReal.rpow_one]
  exact hq0_lt.ne'

中文:
定理 lintegral_rpow_enorm_eq_rpow_eLpNorm'
  条件: {f : α -> ε} (hq0_lt : 0 < q)
  证明: by
  rw [eLpNorm'_eq_lintegral_enorm]; rw [← ENNReal.rpow_mul]; rw [one_div]; rw [inv_mul_cancel₀]; rw [ENNReal.rpow_one]
  exact hq0_lt.ne'

Depends on / 依赖: ENNReal, ENNReal.rpow_mul, ENNReal.rpow_one, _eq_lintegral_enorm, eLpNorm, hq0_lt, hq0_lt.ne, one_div, rpow_mul, rpow_one
-/
theorem lintegral_rpow_enorm_eq_rpow_eLpNorm' {f : α -> ε} (hq0_lt : 0 < q) :
    ∫⁻ a, ‖f a‖ₑ ^ q ∂μ = eLpNorm' f q μ ^ q := by
  rw [eLpNorm'_eq_lintegral_enorm]; rw [← ENNReal.rpow_mul]; rw [one_div]; rw [inv_mul_cancel₀]; rw [ENNReal.rpow_one]
  exact hq0_lt.ne'

/--
lemma `eLpNorm_nnreal_pow_eq_lintegral` / 引理 `eLpNorm_nnreal_pow_eq_lintegral`

English:
lemma eLpNorm_nnreal_pow_eq_lintegral
  given: {f : α -> ε} {p : Real>=0} (hp : p != 0)
  proof: by
  simp [eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp)]

中文:
引理 eLpNorm_nnreal_pow_eq_lintegral
  条件: {f : α -> ε} {p : 实数>=0} (hp : p != 0)
  证明: by
  simp [eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp)]

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, NNReal, NNReal.coe_pos.trans, coe_ne_top, coe_pos, eLpNorm_eq_eLpNorm, lintegral_rpow_enorm_eq_rpow_eLpNorm, pos_iff_ne_zero
-/
lemma eLpNorm_nnreal_pow_eq_lintegral {f : α -> ε} {p : Real>=0} (hp : p != 0) :
    eLpNorm f p μ ^ (p : Real) = ∫⁻ x, ‖f x‖ₑ ^ (p : Real) ∂μ := by
  simp [eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp)]

/--
Definition of `lpNorm` / `lpNorm` 的定义

English:
definition lpNorm
  signature: (f : α -> E) (p : Real>=0∞) (μ : Measure α)
  body: open scoped Classical in if AEStronglyMeasurable f μ then (eLpNorm f p μ).toReal else 0

中文:
定义 lpNorm
  签名: (f : α -> E) (p : 实数>=0∞) (μ : 测度 α)
  定义体: open scoped Classical in if AEStronglyMeasurable f μ then (eLpNorm f p μ).toReal else 0

Depends on / 依赖: AEStronglyMeasurable, Classical, eLpNorm, scoped, toReal
-/
noncomputable def lpNorm (f : α -> E) (p : Real>=0∞) (μ : Measure α) : Real :=
  open scoped Classical in if AEStronglyMeasurable f μ then (eLpNorm f p μ).toReal else 0

end Lp

end MeasureTheory
