/-
Copyright (c) 2022 Rishikesh Vaishnav. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rishikesh Vaishnav
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Conditional Probability

This file defines conditional probability and includes basic results relating to it.

Given some measure `μ` defined on a measure space on some type `Ω` and some `s : Set Ω`,
we define the measure of `μ` conditioned on `s` as the restricted measure scaled by
the inverse of the measure of `s`: `cond μ s = (μ s)⁻¹ • μ.restrict s`. The scaling
ensures that this is a probability measure (when `μ` is a finite measure).

From this definition, we derive the "axiomatic" definition of conditional probability
based on application: for any `s t : Set Ω`, we have `μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)`.

## Main Statements

* `cond_cond_eq_cond_inter`: conditioning on one set and then another is equivalent
  to conditioning on their intersection.
* `cond_eq_inv_mul_cond_mul`: Bayes' Theorem, `μ[t | s] = (μ s)⁻¹ * μ[s | t] * (μ t)`.

## Notation

This file uses the notation `μ[|s]` the measure of `μ` conditioned on `s`,
and `μ[t | s]` for the probability of `t` given `s` under `μ` (equivalent to the
application `μ[|s] t`).

These notations are contained in the scope `ProbabilityTheory`.

## Implementation notes

Because we have the alternative measure restriction application principles
`Measure.restrict_apply` and `Measure.restrict_apply'`, which require
measurability of the restricted and restricting sets, respectively,
many of the theorems here will have corresponding alternatives as well.
For the sake of brevity, we've chosen to only go with `Measure.restrict_apply'`
for now, but the alternative theorems can be added if needed.

Use of `@[simp]` generally follows the rule of removing conditions on a measure
when possible.

Hypotheses that are used to "define" a conditional distribution by requiring that
the conditioning set has non-zero measure should be named using the abbreviation
"c" (which stands for "conditionable") rather than "nz". For example `(hci : μ (s ∩ t) ≠ 0)`
(rather than `hnzi`) should be used for a hypothesis ensuring that `μ[|s ∩ t]` is defined.

## Tags

conditional, conditioned, bayes
-/

@[expose] public section

noncomputable section

open ENNReal MeasureTheory MeasureTheory.Measure MeasurableSpace Set

variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}

namespace ProbabilityTheory

variable (μ) in
/-- The conditional probability measure of measure `μ` on set `s` is `μ` restricted to `s`
and scaled by the inverse of `μ s` (to make it a probability measure):
`(μ s)⁻¹ • μ.restrict s`. -/
@[wikidata Q327069]
/--
Definition of `cond` / `cond` 的定义

English:
definition cond
  signature: (s : Set Ω)
  body: (μ s)⁻¹ • μ.restrict s

@[inherit_doc ProbabilityTheory.cond]
scoped macro:max μ:term noWs "[|" s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s)
@[inherit_doc cond]
scoped macro:max μ:term noWs "[" t:term " | " s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s $t)

中文:
定义 cond
  签名: (s : Set Ω)
  定义体: (μ s)⁻¹ • μ.restrict s

@[inherit_doc ProbabilityTheory.cond]
scoped macro:max μ:term noWs "[|" s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s)
@[inherit_doc cond]
scoped macro:max μ:term noWs "[" t:term " | " s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s $t)

Depends on / 依赖: restrict
-/
def cond (s : Set Ω) : Measure Ω :=
  (μ s)⁻¹ • μ.restrict s

@[inherit_doc ProbabilityTheory.cond]
scoped macro:max μ:term noWs "[|" s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s)
@[inherit_doc cond]
scoped macro:max μ:term noWs "[" t:term " | " s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s $t)

/-!
We can't use `notation` or `notation3` as it does not support `noWs`, and so we have to write
our own delaborators.
-/

section delaborators
open Lean PrettyPrinter.Delaborator SubExpr

/-- Unexpander for `μ[|s]` notation. -/
@[app_unexpander ProbabilityTheory.cond]
meta def condUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $μ $s) => `($μ[|$s])
  | _ => throw ()

/-- info: μ[|s] : Measure Ω -/
#guard_msgs in
#check μ[|s]

/-- Delaborator for `μ[t | s]` notation. -/
@[app_delab DFunLike.coe]
meta def delabCondApplied : Delab :=
whenNotPPOption getPPExplicit whenPPOption getPPNotation withOverApp 6 do
    let e ← getExpr
guard e.isAppOfArity' ``DFunLike.coe 6
guard (e.getArg!' 4).isAppOf' ``ProbabilityTheory.cond
    let t ← withAppArg delab
withAppFn withAppArg do
      let μ ← withNaryArg 2 delab
      let s ← withNaryArg 3 delab
      `($μ[$t|$s])

/-- info: μ[t | s] : ℝ≥0∞ -/
#guard_msgs in
#check μ[t | s]
/-- info: μ[t | s] : ℝ≥0∞ -/
#guard_msgs in
#check μ[|s] t

end delaborators

/-- The conditional probability measure of measure `μ` on `{ω | X ω ∈ s}`.

It is `μ` restricted to `{ω | X ω ∈ s}` and scaled by the inverse of `μ {ω | X ω ∈ s}`
(to make it a probability measure): `(μ {ω | X ω ∈ s})⁻¹ • μ.restrict {ω | X ω ∈ s}`. -/
scoped macro:max μ:term noWs "[|" X:term " in " s:term "]" : term => `($μ[|$X ⁻¹' $s])

/-- The conditional probability measure of measure `μ` on set `{ω | X ω = x}`.

It is `μ` restricted to `{ω | X ω = x}` and scaled by the inverse of `μ {ω | X ω = x}`
(to make it a probability measure): `(μ {ω | X ω = x})⁻¹ • μ.restrict {ω | X ω = x}`. -/
scoped macro:max μ:term noWs "[" s:term " | " X:term " in " t:term "]" : term =>
  `($μ[$s | $X ⁻¹' $t])

/-- The conditional probability measure of measure `μ` on `{ω | X ω = x}`.

It is `μ` restricted to `{ω | X ω = x}` and scaled by the inverse of `μ {ω | X ω = x}`
(to make it a probability measure): `(μ {ω | X ω = x})⁻¹ • μ.restrict {ω | X ω = x}`. -/
scoped macro:max μ:term noWs "[|" X:term " ← " x:term "]" : term => `($μ[|$X in {$x:term}])

/-- The conditional probability measure of measure `μ` on set `{ω | X ω = x}`.

It is `μ` restricted to `{ω | X ω = x}` and scaled by the inverse of `μ {ω | X ω = x}`
(to make it a probability measure): `(μ {ω | X ω = x})⁻¹ • μ.restrict {ω | X ω = x}`. -/
scoped macro:max μ:term noWs "[" s:term " | " X:term " ← " x:term "]" : term =>
  `($μ[$s | $X in {$x:term}])

/--
theorem `cond_isProbabilityMeasure_of_finite` / 定理 `cond_isProbabilityMeasure_of_finite`

English:
theorem cond_isProbabilityMeasure_of_finite
  given: (hcs : μ s != 0) (hs : μ s != ∞)
  proof: ⟨by
    unfold ProbabilityTheory.cond
    simp only [Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hcs hs⟩

中文:
定理 cond_isProbabilityMeasure_of_finite
  条件: (hcs : μ s != 0) (hs : μ s != ∞)
  证明: ⟨by
    unfold ProbabilityTheory.cond
    simp only [Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hcs hs⟩

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, MeasurableSet, MeasurableSet.univ, Measure, Measure.coe_smul, Measure.restrict_apply, Pi.smul_apply, ProbabilityTheory, ProbabilityTheory.cond, Set.univ_inter, coe_smul, inv_mul_cancel, restrict_apply, smul_apply, smul_eq_mul, univ_inter
-/
theorem cond_isProbabilityMeasure_of_finite (hcs : μ s != 0) (hs : μ s != ∞) :
    IsProbabilityMeasure μ[|s] :=
  ⟨by
    unfold ProbabilityTheory.cond
    simp only [Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hcs hs⟩

/--
theorem `cond_isProbabilityMeasure` / 定理 `cond_isProbabilityMeasure`

English:
theorem cond_isProbabilityMeasure
  given: [IsFiniteMeasure μ] (hcs : μ s != 0)
  proof: cond_isProbabilityMeasure_of_finite hcs (measure_ne_top μ s)

中文:
定理 cond_isProbabilityMeasure
  条件: [IsFiniteMeasure μ] (hcs : μ s != 0)
  证明: cond_isProbabilityMeasure_of_finite hcs (measure_ne_top μ s)

Depends on / 依赖: cond_isProbabilityMeasure_of_finite, measure_ne_top
-/
theorem cond_isProbabilityMeasure [IsFiniteMeasure μ] (hcs : μ s != 0) :
    IsProbabilityMeasure μ[|s] := cond_isProbabilityMeasure_of_finite hcs (measure_ne_top μ s)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroOrProbabilityMeasure μ[|s]
  body: by
  constructor
  simp only [cond, Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
    univ_inter, smul_eq_mul, ← ENNReal.div_eq_inv_mul]
  rcases eq_or_ne (μ s) 0 with h | h
  · simp [h]
  rcases eq_or_ne (μ s) ∞ with h' | h'
  · simp [h']
  simp [ENNReal.div_self h h'

中文:
实例 :
  签名: IsZeroOrProbabilityMeasure μ[|s]
  定义体: by
  constructor
  simp only [cond, Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
    univ_inter, smul_eq_mul, ← ENNReal.div_eq_inv_mul]
  rcases eq_or_ne (μ s) 0 with h | h
  · simp [h]
  rcases eq_or_ne (μ s) ∞ with h' | h'
  · simp [h']
  simp [ENNReal.div_self h h'

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, ENNReal.div_self, MeasurableSet, MeasurableSet.univ, Measure, Measure.coe_smul, Measure.restrict_apply, Pi.smul_apply, coe_smul, div_eq_inv_mul, div_self, eq_or_ne, restrict_apply, smul_apply, smul_eq_mul, univ_inter
-/
instance : IsZeroOrProbabilityMeasure μ[|s] := by
  constructor
  simp only [cond, Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
    univ_inter, smul_eq_mul, ← ENNReal.div_eq_inv_mul]
  rcases eq_or_ne (μ s) 0 with h | h
  · simp [h]
  rcases eq_or_ne (μ s) ∞ with h' | h'
  · simp [h']
  simp [ENNReal.div_self h h']

variable (μ) in
/--
theorem `cond_toMeasurable_eq` / 定理 `cond_toMeasurable_eq`

English:
theorem cond_toMeasurable_eq
  proof: by
  unfold cond
  by_cases hnt : μ s = ∞
  · simp [hnt]
  · simp [Measure.restrict_toMeasurable hnt]

中文:
定理 cond_toMeasurable_eq
  证明: by
  unfold cond
  by_cases hnt : μ s = ∞
  · simp [hnt]
  · simp [Measure.restrict_toMeasurable hnt]

Depends on / 依赖: Measure, Measure.restrict_toMeasurable, restrict_toMeasurable
-/
theorem cond_toMeasurable_eq :
    μ[|(toMeasurable μ s)] = μ[|s] := by
  unfold cond
  by_cases hnt : μ s = ∞
  · simp [hnt]
  · simp [Measure.restrict_toMeasurable hnt]

/--
lemma `cond_absolutelyContinuous` / 引理 `cond_absolutelyContinuous`

English:
lemma cond_absolutelyContinuous
  statement: μ[|s] ≪ μ
  proof: smul_absolutelyContinuous.trans restrict_le_self.absolutelyContinuous

中文:
引理 cond_absolutelyContinuous
  结论: μ[|s] ≪ μ
  证明: smul_absolutelyContinuous.trans restrict_le_self.absolutelyContinuous

Depends on / 依赖: absolutelyContinuous, restrict_le_self, restrict_le_self.absolutelyContinuous, smul_absolutelyContinuous, smul_absolutelyContinuous.trans
-/
lemma cond_absolutelyContinuous : μ[|s] ≪ μ :=
  smul_absolutelyContinuous.trans restrict_le_self.absolutelyContinuous

/--
lemma `absolutelyContinuous_cond_univ` / 引理 `absolutelyContinuous_cond_univ`

English:
lemma absolutelyContinuous_cond_univ
  given: [IsFiniteMeasure μ]
  statement: μ ≪ μ[|univ]
  proof: by
  rw [cond]; rw [restrict_univ]
  refine absolutelyContinuous_smul ?_
  simp [measure_ne_top]

中文:
引理 absolutelyContinuous_cond_univ
  条件: [IsFiniteMeasure μ]
  结论: μ ≪ μ[|univ]
  证明: by
  rw [cond]; rw [restrict_univ]
  refine absolutelyContinuous_smul ?_
  simp [measure_ne_top]

Depends on / 依赖: absolutelyContinuous_smul, measure_ne_top, restrict_univ
-/
lemma absolutelyContinuous_cond_univ [IsFiniteMeasure μ] : μ ≪ μ[|univ] := by
  rw [cond]; rw [restrict_univ]
  refine absolutelyContinuous_smul ?_
  simp [measure_ne_top]

/--
lemma `ae_cond_of_forall_mem` / 引理 `ae_cond_of_forall_mem`

English:
lemma ae_cond_of_forall_mem
  given: (hs : MeasurableSet s) {p : Ω -> Prop} (h : forall x in s, p x)
  proof: ae_smul_measure (ae_restrict_of_forall_mem hs h) _

中文:
引理 ae_cond_of_forall_mem
  条件: (hs : MeasurableSet s) {p : Ω -> 命题} (h : 对任意 x in s, p x)
  证明: ae_smul_measure (ae_restrict_of_forall_mem hs h) _

Depends on / 依赖: ae_restrict_of_forall_mem, ae_smul_measure
-/
lemma ae_cond_of_forall_mem (hs : MeasurableSet s) {p : Ω -> Prop} (h : forall x in s, p x) :
    forallᵐ x ∂μ[|s], p x := ae_smul_measure (ae_restrict_of_forall_mem hs h) _

/--
lemma `ae_cond_mem₀` / 引理 `ae_cond_mem₀`

English:
lemma ae_cond_mem₀
  given: (hs : NullMeasurableSet s μ)
  statement: forallᵐ x ∂μ[|s], x in s
  proof: ae_smul_measure (ae_restrict_mem₀ hs) _

中文:
引理 ae_cond_mem₀
  条件: (hs : NullMeasurableSet s μ)
  结论: 对任意ᵐ x ∂μ[|s], x in s
  证明: ae_smul_measure (ae_restrict_mem₀ hs) _

Depends on / 依赖: ae_smul_measure
-/
lemma ae_cond_mem₀ (hs : NullMeasurableSet s μ) : forallᵐ x ∂μ[|s], x in s :=
  ae_smul_measure (ae_restrict_mem₀ hs) _

/--
lemma `ae_cond_mem` / 引理 `ae_cond_mem`

English:
lemma ae_cond_mem
  given: (hs : MeasurableSet s)
  statement: forallᵐ x ∂μ[|s], x in s
  proof: ae_smul_measure (ae_restrict_mem hs) _

中文:
引理 ae_cond_mem
  条件: (hs : MeasurableSet s)
  结论: 对任意ᵐ x ∂μ[|s], x in s
  证明: ae_smul_measure (ae_restrict_mem hs) _

Depends on / 依赖: ae_restrict_mem, ae_smul_measure
-/
lemma ae_cond_mem (hs : MeasurableSet s) : forallᵐ x ∂μ[|s], x in s :=
  ae_smul_measure (ae_restrict_mem hs) _

section Bayes

variable (μ) in
/--
lemma `cond_empty` / 引理 `cond_empty`

English:
lemma cond_empty
  statement: μ[|∅] = 0
  proof: by simp [cond]

中文:
引理 cond_empty
  结论: μ[|∅] = 0
  证明: by simp [cond]
-/
@[simp] lemma cond_empty : μ[|∅] = 0 := by simp [cond]

variable (μ) in
/--
lemma `cond_univ` / 引理 `cond_univ`

English:
lemma cond_univ
  given: [IsProbabilityMeasure μ]
  statement: μ[|Set.univ] = μ
  proof: by
  simp [cond, measure_univ, Measure.restrict_univ]

中文:
引理 cond_univ
  条件: [IsProbabilityMeasure μ]
  结论: μ[|Set.univ] = μ
  证明: by
  simp [cond, measure_univ, Measure.restrict_univ]
-/
@[simp] lemma cond_univ [IsProbabilityMeasure μ] : μ[|Set.univ] = μ := by
  simp [cond, measure_univ, Measure.restrict_univ]

/--
lemma `cond_eq_zero` / 引理 `cond_eq_zero`

English:
lemma cond_eq_zero
  statement: μ[|s] = 0 ↔ μ s = ∞ ∨ μ s = 0
  proof: by simp [cond]

中文:
引理 cond_eq_zero
  结论: μ[|s] = 0 ↔ μ s = ∞ ∨ μ s = 0
  证明: by simp [cond]
-/
@[simp] lemma cond_eq_zero : μ[|s] = 0 ↔ μ s = ∞ ∨ μ s = 0 := by simp [cond]

/--
lemma `cond_eq_zero_of_meas_eq_zero` / 引理 `cond_eq_zero_of_meas_eq_zero`

English:
lemma cond_eq_zero_of_meas_eq_zero
  given: (hμs : μ s = 0)
  statement: μ[|s] = 0
  proof: by simp [hμs]

中文:
引理 cond_eq_zero_of_meas_eq_zero
  条件: (hμs : μ s = 0)
  结论: μ[|s] = 0
  证明: by simp [hμs]
-/
lemma cond_eq_zero_of_meas_eq_zero (hμs : μ s = 0) : μ[|s] = 0 := by simp [hμs]

/--
theorem `cond_apply` / 定理 `cond_apply`

English:
theorem cond_apply
  given: (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω)
  proof: by
  rw [cond]; rw [Measure.smul_apply]; rw [Measure.restrict_apply' hms]; rw [Set.inter_comm]; rw [smul_eq_mul]

中文:
定理 cond_apply
  条件: (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω)
  证明: by
  rw [cond]; rw [Measure.smul_apply]; rw [Measure.restrict_apply' hms]; rw [Set.inter_comm]; rw [smul_eq_mul]

Depends on / 依赖: Measure, Measure.restrict_apply, Measure.smul_apply, Set.inter_comm, inter_comm, restrict_apply, smul_apply, smul_eq_mul
-/
theorem cond_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[t | s] = (μ s)⁻¹ * μ (s inter t) := by
  rw [cond]; rw [Measure.smul_apply]; rw [Measure.restrict_apply' hms]; rw [Set.inter_comm]; rw [smul_eq_mul]

/--
theorem `cond_apply'` / 定理 `cond_apply'`

English:
theorem cond_apply'
  given: (ht : MeasurableSet t) (μ : Measure Ω)
  statement: μ[t | s] = (μ s)⁻¹ * μ (s inter t)
  proof: by
  rw [cond]; rw [Measure.smul_apply]; rw [Measure.restrict_apply ht]; rw [Set.inter_comm]; rw [smul_eq_mul]

中文:
定理 cond_apply'
  条件: (ht : MeasurableSet t) (μ : Measure Ω)
  结论: μ[t | s] = (μ s)⁻¹ * μ (s inter t)
  证明: by
  rw [cond]; rw [Measure.smul_apply]; rw [Measure.restrict_apply ht]; rw [Set.inter_comm]; rw [smul_eq_mul]

Depends on / 依赖: Measure, Measure.restrict_apply, Measure.smul_apply, Set.inter_comm, inter_comm, restrict_apply, smul_apply, smul_eq_mul
-/
theorem cond_apply' (ht : MeasurableSet t) (μ : Measure Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t) := by
  rw [cond]; rw [Measure.smul_apply]; rw [Measure.restrict_apply ht]; rw [Set.inter_comm]; rw [smul_eq_mul]

/--
lemma `cond_apply_self` / 引理 `cond_apply_self`

English:
lemma cond_apply_self
  given: (hs₀ : μ s != 0) (hs : μ s != ∞)
  statement: μ[s | s] = 1
  proof: by
  simpa [cond] using ENNReal.inv_mul_cancel hs₀ hs

中文:
引理 cond_apply_self
  条件: (hs₀ : μ s != 0) (hs : μ s != ∞)
  结论: μ[s | s] = 1
  证明: by
  simpa [cond] using ENNReal.inv_mul_cancel hs₀ hs
-/
@[simp] lemma cond_apply_self (hs₀ : μ s != 0) (hs : μ s != ∞) : μ[s | s] = 1 := by
  simpa [cond] using ENNReal.inv_mul_cancel hs₀ hs

/--
theorem `cond_inter_self` / 定理 `cond_inter_self`

English:
theorem cond_inter_self
  given: (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω)
  proof: by
  rw [cond_apply hms]; rw [← Set.inter_assoc]; rw [Set.inter_self]; rw [← cond_apply hms]

中文:
定理 cond_inter_self
  条件: (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω)
  证明: by
  rw [cond_apply hms]; rw [← Set.inter_assoc]; rw [Set.inter_self]; rw [← cond_apply hms]

Depends on / 依赖: Set.inter_assoc, Set.inter_self, cond_apply, inter_assoc, inter_self
-/
theorem cond_inter_self (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) :
    μ[s inter t | s] = μ[t | s] := by
  rw [cond_apply hms]; rw [← Set.inter_assoc]; rw [Set.inter_self]; rw [← cond_apply hms]

/--
theorem `inter_pos_of_cond_ne_zero` / 定理 `inter_pos_of_cond_ne_zero`

English:
theorem inter_pos_of_cond_ne_zero
  given: (hms : MeasurableSet s) (hcst : μ[t | s] != 0)
  proof: by
  refine pos_iff_ne_zero.mpr (right_ne_zero_of_mul (a := (μ s)⁻¹) ?_)
  convert! hcst
  simp [hms, Set.inter_comm, cond]

中文:
定理 inter_pos_of_cond_ne_zero
  条件: (hms : MeasurableSet s) (hcst : μ[t | s] != 0)
  证明: by
  refine pos_iff_ne_zero.mpr (right_ne_zero_of_mul (a := (μ s)⁻¹) ?_)
  convert! hcst
  simp [hms, Set.inter_comm, cond]

Depends on / 依赖: Set.inter_comm, convert, inter_comm, pos_iff_ne_zero, pos_iff_ne_zero.mpr, right_ne_zero_of_mul
-/
theorem inter_pos_of_cond_ne_zero (hms : MeasurableSet s) (hcst : μ[t | s] != 0) :
    0 < μ (s inter t) := by
  refine pos_iff_ne_zero.mpr (right_ne_zero_of_mul (a := (μ s)⁻¹) ?_)
  convert! hcst
  simp [hms, Set.inter_comm, cond]

/--
lemma `cond_pos_of_inter_ne_zero` / 引理 `cond_pos_of_inter_ne_zero`

English:
lemma cond_pos_of_inter_ne_zero
  given: [IsFiniteMeasure μ] (hms : MeasurableSet s) (hci : μ (s inter t) != 0)
  proof: by
  rw [cond_apply hms]
  refine ENNReal.mul_pos ?_ hci
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)

中文:
引理 cond_pos_of_inter_ne_zero
  条件: [IsFiniteMeasure μ] (hms : MeasurableSet s) (hci : μ (s inter t) != 0)
  证明: by
  rw [cond_apply hms]
  refine ENNReal.mul_pos ?_ hci
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)

Depends on / 依赖: ENNReal, ENNReal.inv_ne_zero.mpr, ENNReal.mul_pos, cond_apply, inv_ne_zero, measure_ne_top, mul_pos
-/
lemma cond_pos_of_inter_ne_zero [IsFiniteMeasure μ] (hms : MeasurableSet s) (hci : μ (s inter t) != 0) :
    0 < μ[t | s] := by
  rw [cond_apply hms]
  refine ENNReal.mul_pos ?_ hci
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)

/--
lemma `cond_cond_eq_cond_inter'` / 引理 `cond_cond_eq_cond_inter'`

English:
lemma cond_cond_eq_cond_inter'
  given: (hms : MeasurableSet s) (hmt : MeasurableSet t) (hcs : μ s != ∞)
  proof: by
  ext u
  obtain hst | hst := eq_or_ne (μ (s inter t)) 0
  · have : μ (s inter t inter u) = 0 := measure_mono_null Set.inter_subset_left hst
    simp [cond_apply, *, ← Set.inter_assoc]
  · have hs : μ s != 0 := (measure_pos_of_superset Set.inter_subset_left hst).ne'
    simp [*, hms.inter hmt, co

中文:
引理 cond_cond_eq_cond_inter'
  条件: (hms : MeasurableSet s) (hmt : MeasurableSet t) (hcs : μ s != ∞)
  证明: by
  ext u
  obtain hst | hst := eq_or_ne (μ (s inter t)) 0
  · have : μ (s inter t inter u) = 0 := measure_mono_null Set.inter_subset_left hst
    simp [cond_apply, *, ← Set.inter_assoc]
  · have hs : μ s != 0 := (measure_pos_of_superset Set.inter_subset_left hst).ne'
    simp [*, hms.inter hmt, co

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, ENNReal.mul_inv, Set.inter_assoc, Set.inter_subset_left, cond_apply, eq_or_ne, hms.inter, inter_assoc, inter_subset_left, inv_mul_cancel, measure_mono_null, measure_pos_of_superset, mul_assoc, mul_comm, mul_inv
-/
lemma cond_cond_eq_cond_inter' (hms : MeasurableSet s) (hmt : MeasurableSet t) (hcs : μ s != ∞) :
    μ[|s][|t] = μ[|s inter t] := by
  ext u
  obtain hst | hst := eq_or_ne (μ (s inter t)) 0
  · have : μ (s inter t inter u) = 0 := measure_mono_null Set.inter_subset_left hst
    simp [cond_apply, *, ← Set.inter_assoc]
  · have hs : μ s != 0 := (measure_pos_of_superset Set.inter_subset_left hst).ne'
    simp [*, hms.inter hmt, cond_apply, ← Set.inter_assoc, ENNReal.mul_inv, ← mul_assoc,
      mul_comm _ (μ s)⁻¹, ENNReal.inv_mul_cancel]

/--
theorem `cond_cond_eq_cond_inter` / 定理 `cond_cond_eq_cond_inter`

English:
theorem cond_cond_eq_cond_inter
  statement: (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
  proof: cond_cond_eq_cond_inter' hms hmt (measure_ne_top μ s)

中文:
定理 cond_cond_eq_cond_inter
  结论: (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
  证明: cond_cond_eq_cond_inter' hms hmt (measure_ne_top μ s)

Depends on / 依赖: cond_cond_eq_cond_inter, measure_ne_top
-/
theorem cond_cond_eq_cond_inter (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
    [IsFiniteMeasure μ] : μ[|s][|t] = μ[|s inter t] :=
  cond_cond_eq_cond_inter' hms hmt (measure_ne_top μ s)

/--
theorem `cond_mul_eq_inter'` / 定理 `cond_mul_eq_inter'`

English:
theorem cond_mul_eq_inter'
  given: (hms : MeasurableSet s) (hcs' : μ s != ∞) (t : Set Ω)
  proof: by
  obtain hcs | hcs := eq_or_ne (μ s) 0
  · simp [hcs, measure_inter_null_of_null_left]
  · rw [cond_apply hms, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hcs hcs', one_mul]

中文:
定理 cond_mul_eq_inter'
  条件: (hms : MeasurableSet s) (hcs' : μ s != ∞) (t : Set Ω)
  证明: by
  obtain hcs | hcs := eq_or_ne (μ s) 0
  · simp [hcs, measure_inter_null_of_null_left]
  · rw [cond_apply hms, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hcs hcs', one_mul]

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, cond_apply, eq_or_ne, measure_inter_null_of_null_left, mul_assoc, mul_comm, mul_inv_cancel, one_mul
-/
theorem cond_mul_eq_inter' (hms : MeasurableSet s) (hcs' : μ s != ∞) (t : Set Ω) :
    μ[t | s] * μ s = μ (s inter t) := by
  obtain hcs | hcs := eq_or_ne (μ s) 0
  · simp [hcs, measure_inter_null_of_null_left]
  · rw [cond_apply hms, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hcs hcs', one_mul]

/--
theorem `cond_mul_eq_inter` / 定理 `cond_mul_eq_inter`

English:
theorem cond_mul_eq_inter
  given: (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
  proof: cond_mul_eq_inter' hms (measure_ne_top _ s) t

中文:
定理 cond_mul_eq_inter
  条件: (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
  证明: cond_mul_eq_inter' hms (measure_ne_top _ s) t

Depends on / 依赖: cond_mul_eq_inter, measure_ne_top
-/
theorem cond_mul_eq_inter (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t | s] * μ s = μ (s inter t) := cond_mul_eq_inter' hms (measure_ne_top _ s) t

/--
theorem `cond_add_cond_compl_eq` / 定理 `cond_add_cond_compl_eq`

English:
theorem cond_add_cond_compl_eq
  given: (hms : MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ]
  proof: by
  rw [cond_mul_eq_inter hms]; rw [cond_mul_eq_inter hms.compl]; rw [Set.inter_comm _ t]; rw [Set.inter_comm _ t]
  exact measure_inter_add_sdiff t hms

中文:
定理 cond_add_cond_compl_eq
  条件: (hms : MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ]
  证明: by
  rw [cond_mul_eq_inter hms]; rw [cond_mul_eq_inter hms.compl]; rw [Set.inter_comm _ t]; rw [Set.inter_comm _ t]
  exact measure_inter_add_sdiff t hms

Depends on / 依赖: Set.inter_comm, cond_mul_eq_inter, hms.compl, inter_comm, measure_inter_add_sdiff
-/
theorem cond_add_cond_compl_eq (hms : MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t | s] * μ s + μ[t | sᶜ] * μ sᶜ = μ t := by
  rw [cond_mul_eq_inter hms]; rw [cond_mul_eq_inter hms.compl]; rw [Set.inter_comm _ t]; rw [Set.inter_comm _ t]
  exact measure_inter_add_sdiff t hms

/--
theorem `cond_eq_inv_mul_cond_mul` / 定理 `cond_eq_inv_mul_cond_mul`

English:
theorem cond_eq_inv_mul_cond_mul
  statement: (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
  proof: by
  rw [mul_assoc]; rw [cond_mul_eq_inter hmt s]; rw [Set.inter_comm]; rw [cond_apply hms]

中文:
定理 cond_eq_inv_mul_cond_mul
  结论: (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
  证明: by
  rw [mul_assoc]; rw [cond_mul_eq_inter hmt s]; rw [Set.inter_comm]; rw [cond_apply hms]

Depends on / 依赖: Set.inter_comm, cond_apply, cond_mul_eq_inter, inter_comm, mul_assoc
-/
theorem cond_eq_inv_mul_cond_mul (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
    [IsFiniteMeasure μ] : μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t := by
  rw [mul_assoc]; rw [cond_mul_eq_inter hmt s]; rw [Set.inter_comm]; rw [cond_apply hms]

end Bayes

/--
lemma `comap_cond` / 引理 `comap_cond`

English:
lemma comap_cond
  statement: {i : Ω' -> Ω} (hi : MeasurableEmbedding i) (hi' : forallᵐ ω ∂μ, ω in range i)
  proof: by
  ext t ht
  change μ (range i)ᶜ = 0 at hi'
  rw [cond_apply]; rw [comap_apply]; rw [cond_apply]; rw [comap_apply]; rw [comap_apply]; rw [image_inter]; rw [image_preimage_eq_inter_range]; rw [inter_right_comm]; rw [measure_inter_conull hi']; rw [measure_inter_conull hi']
  all_goals first
  | exa

中文:
引理 comap_cond
  结论: {i : Ω' -> Ω} (hi : MeasurableEmbedding i) (hi' : 对任意ᵐ ω ∂μ, ω in range i)
  证明: by
  ext t ht
  change μ (range i)ᶜ = 0 at hi'
  rw [cond_apply]; rw [comap_apply]; rw [cond_apply]; rw [comap_apply]; rw [comap_apply]; rw [image_inter]; rw [image_preimage_eq_inter_range]; rw [inter_right_comm]; rw [measure_inter_conull hi']; rw [measure_inter_conull hi']
  all_goals first
  | exa

Depends on / 依赖: NonUnitalSubsemiringClass, NonUnitalSubsemiringClass.toNonUnitalNonAssocSemiring, Subsemigroup, Subsemigroup.center.commSemigroup, all_goals, center, comap_apply, commSemigroup, cond_apply, hi.injective, hi.measurable, hi.measurableSet_image, image_inter, image_preimage_eq_inter_range, injective, inter_right_comm, measurable, measurableSet_image, measure_inter_conull, toNonUnitalNonAssocSemiring
-/
lemma comap_cond {i : Ω' -> Ω} (hi : MeasurableEmbedding i) (hi' : forallᵐ ω ∂μ, ω in range i)
    (hs : MeasurableSet s) : comap i μ[|s] = (comap i μ)[|i in s] := by
  ext t ht
  change μ (range i)ᶜ = 0 at hi'
  rw [cond_apply]; rw [comap_apply]; rw [cond_apply]; rw [comap_apply]; rw [comap_apply]; rw [image_inter]; rw [image_preimage_eq_inter_range]; rw [inter_right_comm]; rw [measure_inter_conull hi']; rw [measure_inter_conull hi']
  all_goals first
  | exact hi.injective
  | exact hi.measurableSet_image'
  | exact hs
  | exact ht
  | exact hi.measurable hs
  | exact (hi.measurable hs).inter ht

variable [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/--
lemma `sum_meas_smul_cond_fiber` / 引理 `sum_meas_smul_cond_fiber`

English:
lemma sum_meas_smul_cond_fiber
  given: {X : Ω -> α} (hX : Measurable X) (μ : Measure Ω) [IsFiniteMeasure μ]
  proof: by
  ext E hE
  calc
    _ = ∑ x, μ (X ⁻¹' {x} inter E) := by
      simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (μ _), cond_mul_eq_inter (hX (.singleton _))]
    _ = _ := by
      have : ⋃ x in Finset.univ, X ⁻¹' {

中文:
引理 sum_meas_smul_cond_fiber
  条件: {X : Ω -> α} (hX : Measurable X) (μ : Measure Ω) [IsFiniteMeasure μ]
  证明: by
  ext E hE
  calc
    _ = ∑ x, μ (X ⁻¹' {x} inter E) := by
      simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (μ _), cond_mul_eq_inter (hX (.singleton _))]
    _ = _ := by
      have : ⋃ x in Finset.univ, X ⁻¹' {

Depends on / 依赖: Finset, Finset.sum_apply, Finset.univ, Function, Function.onFun, Measure, Measure.coe_finsetSum, Measure.coe_smul, Pairwise, PairwiseDisjoint, Pi.smul_apply, Set.Pairwise, coe_finsetSum, coe_smul, cond_mul_eq_inter, disjoint_left, measure_biUnion_finset, mul_comm, simp_rw, singleton
-/
lemma sum_meas_smul_cond_fiber {X : Ω -> α} (hX : Measurable X) (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x, μ (X ⁻¹' {x}) • μ[|X ← x] = μ := by
  ext E hE
  calc
    _ = ∑ x, μ (X ⁻¹' {x} inter E) := by
      simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (μ _), cond_mul_eq_inter (hX (.singleton _))]
    _ = _ := by
      have : ⋃ x in Finset.univ, X ⁻¹' {x} inter E = E := by ext; simp
      rw [← measure_biUnion_finset _ fun _ _ => (hX (.singleton _)).inter hE]; rw [this]
      aesop (add simp [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left])

end ProbabilityTheory
