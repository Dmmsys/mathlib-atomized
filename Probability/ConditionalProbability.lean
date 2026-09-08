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
/-
**ProbabilityTheory.cond** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：cond (s : Set Ω) : Measure Ω
参数：s : Set Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conditional probability measure of measure `μ` on set `s` is `μ` restricted 
to `s`
and scaled by the inverse of `μ s` (to make it a probability measure):
`(μ s)⁻¹ • μ.restrict s`.
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
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 6 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``DFunLike.coe 6
    guard <| (e.getArg!' 4).isAppOf' ``ProbabilityTheory.cond
    let t ← withAppArg delab
    withAppFn <| withAppArg do
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

/-- The conditional probability measure of any measure on any set of finite positive measure
is a probability measure. -/
/-
**ProbabilityTheory.cond_isProbabilityMeasure_of_finite** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：cond_isProbabilityMeasure_of_finite (hcs : μ s != 0) (hs : μ s != ∞) : IsP
robabilityMeasure μ[|s]
参数：hcs : μ s != 0；hs : μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1

--- 原说明 ---
The conditional probability measure of any measure on any set of finite positive
 measure
is a probability measure.
-/
theorem cond_isProbabilityMeasure_of_finite (hcs : μ s ≠ 0) (hs : μ s ≠ ∞) :
    IsProbabilityMeasure μ[|s] :=
  ⟨by
    unfold ProbabilityTheory.cond
    simp only [Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hcs hs⟩

/-- The conditional probability measure of any finite measure on any set of positive measure
is a probability measure. -/
/-
**ProbabilityTheory.cond_isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：cond_isProbabilityMeasure [IsFiniteMeasure μ] (hcs : μ s != 0) : IsProbabi
lityMeasure μ[|s]
参数：hcs : μ s != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.cond_isProbabilityMeasure_of_finite`：cond_isProbabilit
yMeasure_of_finite (hcs : μ s != 0) (hs : μ s != ∞) : IsProbabilityMeasure μ[|s]
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞

--- 原说明 ---
The conditional probability measure of any finite measure on any set of positive
 measure
is a probability measure.
-/
theorem cond_isProbabilityMeasure [IsFiniteMeasure μ] (hcs : μ s ≠ 0) :
    IsProbabilityMeasure μ[|s] := cond_isProbabilityMeasure_of_finite hcs (measure_ne_top μ s)
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**ProbabilityTheory.cond_toMeasurable_eq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：cond_toMeasurable_eq : μ[|(toMeasurable μ s)] = μ[|s]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.restrict_toMeasurable`：restrict_toMeasurable (h : 
μ s != ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s
-/
theorem cond_toMeasurable_eq :
    μ[|(toMeasurable μ s)] = μ[|s] := by
  unfold cond
  by_cases hnt : μ s = ∞
  · simp [hnt]
  · simp [Measure.restrict_toMeasurable hnt]
/-
**ProbabilityTheory.cond_absolutelyContinuous** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：cond_absolutelyContinuous : μ[|s] ≪ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
lemma cond_absolutelyContinuous : μ[|s] ≪ μ :=
  smul_absolutelyContinuous.trans restrict_le_self.absolutelyContinuous
/-
**ProbabilityTheory.absolutelyContinuous_cond_univ** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：absolutelyContinuous_cond_univ [IsFiniteMeasure μ] : μ ≪ μ[|univ]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (μ
 : MeasureTheory.Measure Ω) (s : Set Ω), μ[|s] = (μ s)⁻¹ • μ.restrict s
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma absolutelyContinuous_cond_univ [IsFiniteMeasure μ] : μ ≪ μ[|univ] := by
  rw [cond, restrict_univ]
  refine absolutelyContinuous_smul ?_
  simp [measure_ne_top]
/-
**ProbabilityTheory.ae_cond_of_forall_mem** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：ae_cond_of_forall_mem (hs : MeasurableSet s) {p : Ω -> Prop} (h : forall x
 in s, p x) : forallᵐ x ∂μ[|s], p x
参数：hs : MeasurableSet s；h : forall x in s, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ae_smul_measure`：ae_smul_measure {p : α -> Prop} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : forallᵐ x ∂μ, p x) (c 
: R) : forallᵐ x ∂c • μ, p …
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
-/
lemma ae_cond_of_forall_mem (hs : MeasurableSet s) {p : Ω → Prop} (h : ∀ x ∈ s, p x) :
    ∀ᵐ x ∂μ[|s], p x := ae_smul_measure (ae_restrict_of_forall_mem hs h) _
/-
**ProbabilityTheory.ae_cond_mem** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：ae_cond_mem (hs : MeasurableSet s) : forallᵐ x ∂μ[|s], x in s
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ae_smul_measure`：ae_smul_measure {p : α -> Prop} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : forallᵐ x ∂μ, p x) (c 
: R) : forallᵐ x ∂c • μ, p …
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
-/
lemma ae_cond_mem₀ (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ[|s], x ∈ s :=
  ae_smul_measure (ae_restrict_mem₀ hs) _
/-
**ProbabilityTheory.ae_cond_mem** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：ae_cond_mem (hs : MeasurableSet s) : forallᵐ x ∂μ[|s], x in s
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ae_smul_measure`：ae_smul_measure {p : α -> Prop} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : forallᵐ x ∂μ, p x) (c 
: R) : forallᵐ x ∂c • μ, p …
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
-/
lemma ae_cond_mem (hs : MeasurableSet s) : ∀ᵐ x ∂μ[|s], x ∈ s :=
  ae_smul_measure (ae_restrict_mem hs) _

section Bayes

variable (μ) in
/-
**ProbabilityTheory.cond_empty** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (μ : MeasureTheory.Measure Ω), μ[
|∅] = 0
参数：μ : MeasureTheory.Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma cond_empty : μ[|∅] = 0 := by simp [cond]

variable (μ) in
/-
**ProbabilityTheory.cond_univ** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (μ : MeasureTheory.Measure Ω) [Me
asureTheory.IsProbabilityMeasure μ],   μ[|Set.univ] = μ
参数：μ : MeasureTheory.Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma cond_univ [IsProbabilityMeasure μ] : μ[|Set.univ] = μ := by
  simp [cond, measure_univ, Measure.restrict_univ]
/-
**ProbabilityTheory.cond_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {s 
: Set Ω}, μ[|s] = 0 ↔ μ s = ⊤ ∨ μ s = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma cond_eq_zero : μ[|s] = 0 ↔ μ s = ∞ ∨ μ s = 0 := by simp [cond]
/-
**ProbabilityTheory.cond_eq_zero_of_meas_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：cond_eq_zero_of_meas_eq_zero (hμs : μ s = 0) : μ[|s] = 0
参数：hμs : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma cond_eq_zero_of_meas_eq_zero (hμs : μ s = 0) : μ[|s] = 0 := by simp [hμs]

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
/-
**ProbabilityTheory.cond_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cond_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) : μ[t | s] 
= (μ s)⁻¹ * μ (s inter t)
参数：hms : MeasurableSet s；μ : Measure Ω；t : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (μ
 : MeasureTheory.Measure Ω) (s : Set Ω), μ[|s] = (μ s)⁻¹ • μ.restrict s
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b

--- 原说明 ---
The axiomatic definition of conditional probability derived from a measure-theor
etic one.
-/
theorem cond_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[t | s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply' hms, Set.inter_comm, smul_eq_mul]
/-
**ProbabilityTheory.cond_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cond_apply' (ht : MeasurableSet t) (μ : Measure Ω) : μ[t | s] = (μ s)⁻¹ * 
μ (s inter t)
参数：ht : MeasurableSet t；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (μ
 : MeasureTheory.Measure Ω) (s : Set Ω), μ[|s] = (μ s)⁻¹ • μ.restrict s
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
theorem cond_apply' (ht : MeasurableSet t) (μ : Measure Ω) : μ[t | s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply ht, Set.inter_comm, smul_eq_mul]
/-
**ProbabilityTheory.cond_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {s 
: Set Ω}, μ s ≠ 0 → μ s ≠ ⊤ → μ[s | s] = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply_self`：restrict_apply_self (s : Set 
α) : (μ.restrict s) s = μ s
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
-/
@[simp] lemma cond_apply_self (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) : μ[s | s] = 1 := by
  simpa [cond] using ENNReal.inv_mul_cancel hs₀ hs
/-
**ProbabilityTheory.cond_inter_self** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：cond_inter_self (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) : μ[s 
inter t | s] = μ[t | s]
参数：hms : MeasurableSet s；t : Set Ω；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
theorem cond_inter_self (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) :
    μ[s ∩ t | s] = μ[t | s] := by
  rw [cond_apply hms, ← Set.inter_assoc, Set.inter_self, ← cond_apply hms]
/-
**ProbabilityTheory.inter_pos_of_cond_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：inter_pos_of_cond_ne_zero (hms : MeasurableSet s) (hcst : μ[t | s] != 0) :
 0 < μ (s inter t)
参数：hms : MeasurableSet s；hcst : μ[t | s] != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inter_pos_of_cond_ne_zero (hms : MeasurableSet s) (hcst : μ[t | s] ≠ 0) :
    0 < μ (s ∩ t) := by
  refine pos_iff_ne_zero.mpr (right_ne_zero_of_mul (a := (μ s)⁻¹) ?_)
  convert! hcst
  simp [hms, Set.inter_comm, cond]
/-
**ProbabilityTheory.cond_pos_of_inter_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：cond_pos_of_inter_ne_zero [IsFiniteMeasure μ] (hms : MeasurableSet s) (hci
 : μ (s inter t) != 0) : 0 < μ[t | s]
参数：hms : MeasurableSet s；hci : μ (s inter t) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `ENNReal.mul_pos`：mul_pos (ha : a != 0) (hb : b != 0) : 0 < a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_zero`：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
lemma cond_pos_of_inter_ne_zero [IsFiniteMeasure μ] (hms : MeasurableSet s) (hci : μ (s ∩ t) ≠ 0) :
    0 < μ[t | s] := by
  rw [cond_apply hms]
  refine ENNReal.mul_pos ?_ hci
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
/-
**ProbabilityTheory.cond_cond_eq_cond_inter'** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：cond_cond_eq_cond_inter' (hms : MeasurableSet s) (hmt : MeasurableSet t) (
hcs : μ s != ∞) : μ[|s][|t] = μ[|s inter t]
参数：hms : MeasurableSet s；hmt : MeasurableSet t；hcs : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_pos_of_superset`：measure_pos_of_superset (h : s su
bseteq t) (hs : μ s != 0) : 0 < μ t
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
lemma cond_cond_eq_cond_inter' (hms : MeasurableSet s) (hmt : MeasurableSet t) (hcs : μ s ≠ ∞) :
    μ[|s][|t] = μ[|s ∩ t] := by
  ext u
  obtain hst | hst := eq_or_ne (μ (s ∩ t)) 0
  · have : μ (s ∩ t ∩ u) = 0 := measure_mono_null Set.inter_subset_left hst
    simp [cond_apply, *, ← Set.inter_assoc]
  · have hs : μ s ≠ 0 := (measure_pos_of_superset Set.inter_subset_left hst).ne'
    simp [*, hms.inter hmt, cond_apply, ← Set.inter_assoc, ENNReal.mul_inv, ← mul_assoc,
      mul_comm _ (μ s)⁻¹, ENNReal.inv_mul_cancel]

/-- Conditioning first on `s` and then on `t` results in the same measure as conditioning
on `s ∩ t`. -/
/-
**ProbabilityTheory.cond_cond_eq_cond_inter** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：cond_cond_eq_cond_inter (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ
 : Measure Ω) [IsFiniteMeasure μ] : μ[|s][|t] = μ[|s inter t]
参数：hms : MeasurableSet s；hmt : MeasurableSet t；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.cond_cond_eq_cond_inter'`：cond_cond_eq_cond_inter' (hm
s : MeasurableSet s) (hmt : MeasurableSet t) (hcs : μ s != ∞) : μ[|s][|t] = μ[|s
 inter t]
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞

--- 原说明 ---
Conditioning first on `s` and then on `t` results in the same measure as conditi
oning
on `s ∩ t`.
-/
theorem cond_cond_eq_cond_inter (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
    [IsFiniteMeasure μ] : μ[|s][|t] = μ[|s ∩ t] :=
  cond_cond_eq_cond_inter' hms hmt (measure_ne_top μ s)
/-
**ProbabilityTheory.cond_mul_eq_inter'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：cond_mul_eq_inter' (hms : MeasurableSet s) (hcs' : μ s != ∞) (t : Set Ω) :
 μ[t | s] * μ s = μ (s inter t)
参数：hms : MeasurableSet s；hcs' : μ s != ∞；t : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.measure_inter_null_of_null_left`：measure_inter_null_of_nul
l_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S inter T) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem cond_mul_eq_inter' (hms : MeasurableSet s) (hcs' : μ s ≠ ∞) (t : Set Ω) :
    μ[t | s] * μ s = μ (s ∩ t) := by
  obtain hcs | hcs := eq_or_ne (μ s) 0
  · simp [hcs, measure_inter_null_of_null_left]
  · rw [cond_apply hms, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hcs hcs', one_mul]
/-
**ProbabilityTheory.cond_mul_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：cond_mul_eq_inter (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) [IsF
initeMeasure μ] : μ[t | s] * μ s = μ (s inter t)
参数：hms : MeasurableSet s；t : Set Ω；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.cond_mul_eq_inter'`：cond_mul_eq_inter' (hms : Measurab
leSet s) (hcs' : μ s != ∞) (t : Set Ω) : μ[t | s] * μ s = μ (s inter t)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem cond_mul_eq_inter (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t | s] * μ s = μ (s ∩ t) := cond_mul_eq_inter' hms (measure_ne_top _ s) t

/-- A version of the law of total probability. -/
/-
**ProbabilityTheory.cond_add_cond_compl_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：cond_add_cond_compl_eq (hms : MeasurableSet s) (μ : Measure Ω) [IsFiniteMe
asure μ] : μ[t | s] * μ s + μ[t | sᶜ] * μ sᶜ = μ t
参数：hms : MeasurableSet s；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_mul_eq_inter`：cond_mul_eq_inter (hms : Measurable
Set s) (t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] : μ[t | s] * μ s = μ (s i
nter t)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s

--- 原说明 ---
A version of the law of total probability.
-/
theorem cond_add_cond_compl_eq (hms : MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t | s] * μ s + μ[t | sᶜ] * μ sᶜ = μ t := by
  rw [cond_mul_eq_inter hms, cond_mul_eq_inter hms.compl, Set.inter_comm _ t,
    Set.inter_comm _ t]
  exact measure_inter_add_sdiff t hms

/-- **Bayes' Theorem** -/
/-
**ProbabilityTheory.cond_eq_inv_mul_cond_mul** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：cond_eq_inv_mul_cond_mul (hms : MeasurableSet s) (hmt : MeasurableSet t) (
μ : Measure Ω) [IsFiniteMeasure μ] : μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t
参数：hms : MeasurableSet s；hmt : MeasurableSet t；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ProbabilityTheory.cond_mul_eq_inter`：cond_mul_eq_inter (hms : Measurable
Set s) (t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] : μ[t | s] * μ s = μ (s i
nter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)

--- 原说明 ---
**Bayes' Theorem**
-/
theorem cond_eq_inv_mul_cond_mul (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
    [IsFiniteMeasure μ] : μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t := by
  rw [mul_assoc, cond_mul_eq_inter hmt s, Set.inter_comm, cond_apply hms]

end Bayes

/-
**ProbabilityTheory.comap_cond** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：comap_cond {i : Ω' -> Ω} (hi : MeasurableEmbedding i) (hi' : forallᵐ ω ∂μ,
 ω in range i) (hs : MeasurableSet s) : comap i μ[|s] = (comap i μ)[|i in s]
参数：hi : MeasurableEmbedding i；hi' : forallᵐ ω ∂μ, ω in range i；hs : MeasurableSe
t s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_apply`：cond_apply (hms : MeasurableSet s) (μ : Me
asure Ω) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.inter_right_comm`：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ 
inter s₃ = s₁ inter s₃ inter s₂
· 使用引理 `MeasureTheory.measure_inter_conull`：measure_inter_conull (ht : μ tᶜ = 0)
 : μ (s inter t) = μ s
-/
lemma comap_cond {i : Ω' → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ ω ∂μ, ω ∈ range i)
    (hs : MeasurableSet s) : comap i μ[|s] = (comap i μ)[|i in s] := by
  ext t ht
  change μ (range i)ᶜ = 0 at hi'
  rw [cond_apply, comap_apply, cond_apply, comap_apply, comap_apply, image_inter,
    image_preimage_eq_inter_range, inter_right_comm, measure_inter_conull hi',
    measure_inter_conull hi']
  all_goals first
  | exact hi.injective
  | exact hi.measurableSet_image'
  | exact hs
  | exact ht
  | exact hi.measurable hs
  | exact (hi.measurable hs).inter ht

variable [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- The **law of total probability** for a random variable taking finitely many values: a measure
`μ` can be expressed as a linear combination of its conditional measures `μ[|X ← x]` on fibers of a
random variable `X` valued in a fintype. -/
/-
**ProbabilityTheory.sum_meas_smul_cond_fiber** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：sum_meas_smul_cond_fiber {X : Ω -> α} (hX : Measurable X) (μ : Measure Ω) 
[IsFiniteMeasure μ] : ∑ x, μ (X ⁻¹' {x}) • μ[|X ← x] = μ
参数：hX : Measurable X；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.Measure.coe_finsetSum`：coe_finsetSum {_m : MeasurableSpace
 α} (I : Finset ι) (μ : ι -> Measure α) : ⇑(∑ i in I, μ i) = ∑ i in I, ⇑(μ i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ProbabilityTheory.cond_mul_eq_inter`：cond_mul_eq_inter (hms : Measurable
Set s) (t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] : μ[t | s] * μ s = μ (s i
nter t)
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `DiscreteMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [in
st : MeasurableSpace α] [DiscreteMeasurableSpace α], MeasurableSingletonClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_biUnion_finset`：measure_biUnion_finset {s : Finset
 ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f) (hm : forall b in s, Measura
bleSet (f b)) : μ (⋃ b in …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The **law of total probability** for a random variable taking finitely many valu
es: a measure
`μ` can be expressed as a linear combination of its conditional measures `μ[|X ←
 x]` on fibers of a
random variable `X` valued in a fintype.
-/
lemma sum_meas_smul_cond_fiber {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x, μ (X ⁻¹' {x}) • μ[|X ← x] = μ := by
  ext E hE
  calc
    _ = ∑ x, μ (X ⁻¹' {x} ∩ E) := by
      simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (μ _), cond_mul_eq_inter (hX (.singleton _))]
    _ = _ := by
      have : ⋃ x ∈ Finset.univ, X ⁻¹' {x} ∩ E = E := by ext; simp
      rw [← measure_biUnion_finset _ fun _ _ ↦ (hX (.singleton _)).inter hE, this]
      aesop (add simp [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left])

end ProbabilityTheory

