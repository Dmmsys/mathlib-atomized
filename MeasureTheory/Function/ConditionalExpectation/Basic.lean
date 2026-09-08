/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
public import Mathlib.Tactic.CrossRefAttribute

import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! # Conditional expectation

We build the conditional expectation of an integrable function `f` with value in a Banach space
with respect to a measure `μ` (defined on a measurable space structure `m₀`) and a measurable space
structure `m` with `hm : m ≤ m₀` (a sub-sigma-algebra). This is an `m`-strongly measurable
function `μ[f | m]` which is integrable and verifies `∫ x in s, μ[f | m] x ∂μ = ∫ x in s, f x ∂μ`
for all `m`-measurable sets `s`. It is unique as an element of `L¹`.

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condExpL1CLM` applied to `[f]`, the equivalence class of `f` in `L¹`.

The first step is done in `MeasureTheory.Function.ConditionalExpectation.CondexpL2`, the two
next steps in `MeasureTheory.Function.ConditionalExpectation.CondexpL1` and the final step is
performed in this file.

## Main results

The conditional expectation and its properties

* `condExp (m : MeasurableSpace α) (μ : Measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condExp` : `condExp` is integrable.
* `stronglyMeasurable_condExp` : `condExp` is `m`-strongly-measurable.
* `setIntegral_condExp (hf : Integrable f μ) (hs : MeasurableSet[m] s)` : if `m ≤ m₀` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condExp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condExp` is function-valued, we also define `condExpL1` with value in `L1` and a continuous
linear map `condExpL1CLM` from `L1` to `L1`. `condExp` should be used in most cases.

Uniqueness of the conditional expectation

* `ae_eq_condExp_of_forall_setIntegral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condExp`.

## Notation

For a measure `μ` defined on a measurable space structure `m₀`, another measurable space structure
`m` with `hm : m ≤ m₀` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f | m] = condExp m μ f`.

## TODO

See https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Conditional.20expectation.20of.20product
for how to prove that we can pull `m`-measurable continuous linear maps out of the `m`-conditional
expectation. This would generalise `MeasureTheory.condExp_mul_of_stronglyMeasurable_left`.

## Tags

conditional expectation, conditional expected value

-/

@[expose] public section

open TopologicalSpace MeasureTheory.Lp Filter
open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory
  -- 𝕜 for ℝ or ℂ
  -- E for integrals on a Lp submodule
variable {α β E 𝕜 : Type*} [RCLike 𝕜] {m m₀ : MeasurableSpace α} {μ : Measure α} {f g : α → E}
  {s : Set α}

section NormedAddCommGroup
variable [NormedAddCommGroup E]

section NormedSpace
variable [NormedSpace ℝ E]

open scoped Classical in
variable (m) in
/-- Conditional expectation of a function, with notation `μ[f | m]`.

It is defined as 0 if any one of the following conditions is true:
- `m` is not a sub-σ-algebra of `m₀`,
- `μ` is not σ-finite with respect to `m`,
- `f` is not integrable. -/
@[wikidata Q772232]
noncomputable irreducible_def condExp (μ : Measure[m₀] α) (f : α → E) : α → E :=
  if hm : m ≤ m₀ then
    if h : SigmaFinite (μ.trim hm) ∧ Integrable f μ then
      if StronglyMeasurable[m] f then f
      else have := h.1; aestronglyMeasurable_condExpL1.mk (condExpL1 hm μ f)
    else 0
  else 0

@[inherit_doc MeasureTheory.condExp]
scoped macro:max μ:term noWs "[" f:term " | " m:term "]" : term =>
  `(MeasureTheory.condExp $m $μ $f)

/-- Unexpander for `μ[f | m]` notation. -/
@[app_unexpander MeasureTheory.condExp]
meta def condExpUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $m $μ $f) => `($μ[$f|$m])
  | _ => throw ()

/-- info: μ[f | m] : α → E -/
#guard_msgs in
#check μ[f | m]
/-- info: μ[f | m] sorry : E -/
#guard_msgs in
#check μ[f | m] (sorry : α)

/-
**MeasureTheory.condExp_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_of_not_le (hm_not : ¬m <= m₀) : μ[f | m] = 0
参数：hm_not : ¬m <= m₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL1`：aestronglyMeasurable_condE
xpL1 {f : α -> F'} : AEStronglyMeasurable[m] (condExpL1 hm μ f) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_def`：∀ {α : Type u_5} {E : Type u_6} (m : Measurab
leSpace α) {m₀ : MeasurableSpace α} [inst : NormedAddCommGroup E]   [inst_1 : No
rmedSpace ℝ E] …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem condExp_of_not_le (hm_not : ¬m ≤ m₀) : μ[f | m] = 0 := by rw [condExp, dif_neg hm_not]
/-
**MeasureTheory.condExp_of_not_sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：condExp_of_not_sigmaFinite (hm : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim 
hm)) : μ[f | m] = 0
参数：hm : m <= m₀；hμm_not : ¬SigmaFinite (μ.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL1`：aestronglyMeasurable_condE
xpL1 {f : α -> F'} : AEStronglyMeasurable[m] (condExpL1 hm μ f) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_def`：∀ {α : Type u_5} {E : Type u_6} (m : Measurab
leSpace α) {m₀ : MeasurableSpace α} [inst : NormedAddCommGroup E]   [inst_1 : No
rmedSpace ℝ E] …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
-/
theorem condExp_of_not_sigmaFinite (hm : m ≤ m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) :
    μ[f | m] = 0 := by rw [condExp, dif_pos hm, dif_neg]; push Not; exact fun h => absurd h hμm_not

open scoped Classical in
/-
**MeasureTheory.condExp_of_sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：condExp_of_sigmaFinite (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] : μ[
f | m] = if Integrable f μ then if StronglyMeasurable[m] f then f else aestrongl
yMeasurable_condExpL1.mk (condExpL1 hm μ f) else 0
参数：hm : m <= m₀；μ.trim hm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL1`：aestronglyMeasurable_condE
xpL1 {f : α -> F'} : AEStronglyMeasurable[m] (condExpL1 hm μ f) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_def`：∀ {α : Type u_5} {E : Type u_6} (m : Measurab
leSpace α) {m₀ : MeasurableSpace α} [inst : NormedAddCommGroup E]   [inst_1 : No
rmedSpace ℝ E] …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem condExp_of_sigmaFinite (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] :
    μ[f | m] =
      if Integrable f μ then
        if StronglyMeasurable[m] f then f
        else aestronglyMeasurable_condExpL1.mk (condExpL1 hm μ f)
      else 0 := by
  rw [condExp, dif_pos hm]
  grind
/-
**MeasureTheory.condExp_of_stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：condExp_of_stronglyMeasurable (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm
)] {f : α -> E} (hf : StronglyMeasurable[m] f) (hfi : Integrable f μ) : μ[f | m]
 = f
参数：hm : m <= m₀；μ.trim hm；hf : StronglyMeasurable[m] f；hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL1`：aestronglyMeasurable_condE
xpL1 {f : α -> F'} : AEStronglyMeasurable[m] (condExpL1 hm μ f) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_sigmaFinite`：condExp_of_sigmaFinite (hm : m <= 
m₀) [hμm : SigmaFinite (μ.trim hm)] : μ[f | m] = if Integrable f μ then if Stron
glyMeasurable[m] f then f …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem condExp_of_stronglyMeasurable (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α → E}
    (hf : StronglyMeasurable[m] f) (hfi : Integrable f μ) : μ[f | m] = f := by
  rw [condExp_of_sigmaFinite hm, if_pos hfi, if_pos hf]

@[simp]
/-
**MeasureTheory.condExp_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_const (hm : m <= m₀) (c : E) [IsFiniteMeasure μ] : μ[fun _ : α => 
c | m] = fun _ => c
参数：hm : m <= m₀；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
-/
theorem condExp_const (hm : m ≤ m₀) (c : E) [IsFiniteMeasure μ] :
    μ[fun _ : α ↦ c | m] = fun _ ↦ c :=
  condExp_of_stronglyMeasurable hm stronglyMeasurable_const (integrable_const c)
/-
**MeasureTheory.condExp_ae_eq_condExpL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：condExp_ae_eq_condExpL1 [CompleteSpace E] (hm : m <= m₀) [hμm : SigmaFinit
e (μ.trim hm)] (f : α -> E) : μ[f | m] =ᵐ[μ] condExpL1 hm μ f
参数：hm : m <= m₀；μ.trim hm；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL1`：aestronglyMeasurable_condE
xpL1 {f : α -> F'} : AEStronglyMeasurable[m] (condExpL1 hm μ f) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_sigmaFinite`：condExp_of_sigmaFinite (hm : m <= 
m₀) [hμm : SigmaFinite (μ.trim hm)] : μ[f | m] = if Integrable f μ then if Stron
glyMeasurable[m] f then f …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExpL1_of_aestronglyMeasurable'`：condExpL1_of_aestrongl
yMeasurable' [CompleteSpace F'] (hfm : AEStronglyMeasurable[m] f μ) (hfi : Integ
rable f μ) : condExpL1 hm μ f =ᵐ[μ] f
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.condExpL1_undef`：condExpL1_undef (hf : ¬Integrable f μ) : 
condExpL1 hm μ f = 0
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
-/
theorem condExp_ae_eq_condExpL1 [CompleteSpace E]
    (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α → E) :
    μ[f | m] =ᵐ[μ] condExpL1 hm μ f := by
  rw [condExp_of_sigmaFinite hm]
  by_cases hfi : Integrable f μ
  · rw [if_pos hfi]
    by_cases hfm : StronglyMeasurable[m] f
    · rw [if_pos hfm]
      exact (condExpL1_of_aestronglyMeasurable' hfm.aestronglyMeasurable hfi).symm
    · rw [if_neg hfm]
      exact aestronglyMeasurable_condExpL1.ae_eq_mk.symm
  rw [if_neg hfi, condExpL1_undef hfi]
  exact (coeFn_zero _ _ _).symm
/-
**MeasureTheory.condExp_ae_eq_condExpL1CLM** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：condExp_ae_eq_condExpL1CLM [CompleteSpace E] (hm : m <= m₀) [SigmaFinite (
μ.trim hm)] (hf : Integrable f μ) : μ[f | m] =ᵐ[μ] condExpL1CLM E hm μ (hf.toL1 
f)
参数：hm : m <= m₀；μ.trim hm；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.condExp_ae_eq_condExpL1`：condExp_ae_eq_condExpL1 [Complete
Space E] (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) : μ[f | m] 
=ᵐ[μ] condExpL1 hm μ f
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpL1_eq`：condExpL1_eq [CompleteSpace F'] (hf : Integr
able f μ) : condExpL1 hm μ f = condExpL1CLM F' hm μ (hf.toL1 f)
-/
theorem condExp_ae_eq_condExpL1CLM [CompleteSpace E]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    μ[f | m] =ᵐ[μ] condExpL1CLM E hm μ (hf.toL1 f) := by
  refine (condExp_ae_eq_condExpL1 hm f).trans (Eventually.of_forall fun x => ?_)
  rw [condExpL1_eq hf]
/-
**MeasureTheory.condExp_of_not_integrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：condExp_of_not_integrable (hf : ¬Integrable f μ) : μ[f | m] = 0
参数：hf : ¬Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL1`：aestronglyMeasurable_condE
xpL1 {f : α -> F'} : AEStronglyMeasurable[m] (condExpL1 hm μ f) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_sigmaFinite`：condExp_of_sigmaFinite (hm : m <= 
m₀) [hμm : SigmaFinite (μ.trim hm)] : μ[f | m] = if Integrable f μ then if Stron
glyMeasurable[m] f then f …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
theorem condExp_of_not_integrable (hf : ¬Integrable f μ) : μ[f | m] = 0 := by
  by_cases hm : m ≤ m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  rw [condExp_of_sigmaFinite, if_neg hf]

@[to_fun (attr := simp) condExp_fun_zero]
/-
**MeasureTheory.condExp_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_zero : μ[(0 : α -> E) | m] = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.stronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2} {
x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Zero β],   MeasureT
heory.StronglyMeasurable 0
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
theorem condExp_zero : μ[(0 : α → E) | m] = 0 := by
  by_cases hm : m ≤ m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  exact condExp_of_stronglyMeasurable hm stronglyMeasurable_zero (integrable_zero _ _ _)

@[fun_prop]
/-
**MeasureTheory.stronglyMeasurable_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：stronglyMeasurable_condExp : StronglyMeasurable[m] (μ[f | m])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL1`：aestronglyMeasurable_condE
xpL1 {f : α -> F'} : AEStronglyMeasurable[m] (condExpL1 hm μ f) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_sigmaFinite`：condExp_of_sigmaFinite (hm : m <= 
m₀) [hμm : SigmaFinite (μ.trim hm)] : μ[f | m] = if Integrable f μ then if Stron
glyMeasurable[m] f then f …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.stronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2} {
x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Zero β],   MeasureT
heory.StronglyMeasurable 0
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
theorem stronglyMeasurable_condExp : StronglyMeasurable[m] (μ[f | m]) := by
  by_cases hm : m ≤ m₀
  swap; · rw [condExp_of_not_le hm]; exact stronglyMeasurable_zero
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact stronglyMeasurable_zero
  rw [condExp_of_sigmaFinite hm]
  split_ifs with hfi hfm
  · exact hfm
  · exact aestronglyMeasurable_condExpL1.stronglyMeasurable_mk
  · exact stronglyMeasurable_zero

variable [CompleteSpace E]

@[gcongr]
/-
**MeasureTheory.condExp_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f | m] =ᵐ[μ] μ[g | m]
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_ae_eq_condExpL1`：condExp_ae_eq_condExpL1 [Complete
Space E] (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) : μ[f | m] 
=ᵐ[μ] condExpL1 hm μ f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.condExpL1_congr_ae`：condExpL1_congr_ae (hm : m <= m0) (h :
 f =ᵐ[μ] g) : condExpL1 hm μ f = condExpL1 hm μ g
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
theorem condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f | m] =ᵐ[μ] μ[g | m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm f).trans
    (Filter.EventuallyEq.trans (by rw [condExpL1_congr_ae hm h])
      (condExp_ae_eq_condExpL1 hm g).symm)
/-
**MeasureTheory.condExp_congr_ae_trim** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_congr_ae_trim (hm : m <= m₀) (hfg : f =ᵐ[μ] g) : μ[f | m] =ᵐ[μ.tri
m hm] μ[g | m]
参数：hm : m <= m₀；hfg : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`：ae_eq
_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : 
StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.tri…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
-/
lemma condExp_congr_ae_trim (hm : m ≤ m₀) (hfg : f =ᵐ[μ] g) :
    μ[f | m] =ᵐ[μ.trim hm] μ[g | m] :=
  StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
    stronglyMeasurable_condExp stronglyMeasurable_condExp (condExp_congr_ae hfg)
/-
**MeasureTheory.condExp_of_aestronglyMeasurable'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：condExp_of_aestronglyMeasurable' (hm : m <= m₀) [hμm : SigmaFinite (μ.trim
 hm)] {f : α -> E} (hf : AEStronglyMeasurable[m] f μ) (hfi : Integrable f μ) : μ
[f | m] =ᵐ[μ] f
参数：hm : m <= m₀；μ.trim hm；hf : AEStronglyMeasurable[m] f μ；hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem condExp_of_aestronglyMeasurable' (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α → E}
    (hf : AEStronglyMeasurable[m] f μ) (hfi : Integrable f μ) : μ[f | m] =ᵐ[μ] f := by
  refine ((condExp_congr_ae hf.ae_eq_mk).trans ?_).trans hf.ae_eq_mk.symm
  rw [condExp_of_stronglyMeasurable hm hf.stronglyMeasurable_mk
    ((integrable_congr hf.ae_eq_mk).mp hfi)]

@[fun_prop]
/-
**MeasureTheory.integrable_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_condExp : Integrable (μ[f | m]) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.integrable_condExpL1`：integrable_condExpL1 (f : α -> F') :
 Integrable (condExpL1 hm μ f) μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_ae_eq_condExpL1`：condExp_ae_eq_condExpL1 [Complete
Space E] (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) : μ[f | m] 
=ᵐ[μ] condExpL1 hm μ f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
theorem integrable_condExp : Integrable (μ[f | m]) μ := by
  by_cases hm : m ≤ m₀
  swap; · rw [condExp_of_not_le hm]; exact integrable_zero _ _ _
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact integrable_zero _ _ _
  exact (integrable_condExpL1 f).congr (condExp_ae_eq_condExpL1 hm f).symm

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
/-
**MeasureTheory.setIntegral_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_condExp (hm : m <= m₀) [SigmaFinite (μ.trim hm)] (hf : Integra
ble f μ) (hs : MeasurableSet[m] s) : ∫ x in s, (μ[f | m]) x ∂μ = ∫ x in s, f x ∂
μ
参数：hm : m <= m₀；μ.trim hm；hf : Integrable f μ；hs : MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_ae_eq_condExpL1`：condExp_ae_eq_condExpL1 [Complete
Space E] (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) : μ[f | m] 
=ᵐ[μ] condExpL1 hm μ f
· 使用定理 `MeasureTheory.setIntegral_condExpL1`：setIntegral_condExpL1 [CompleteSpac
e F'] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in s, condExpL1 hm μ
 f x ∂μ = ∫ x in s, f x ∂…

--- 原说明 ---
The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set
 is equal to
the integral of `f` on that set.
-/
theorem setIntegral_condExp (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
    (hs : MeasurableSet[m] s) : ∫ x in s, (μ[f | m]) x ∂μ = ∫ x in s, f x ∂μ := by
  rw [setIntegral_congr_ae (hm s hs) ((condExp_ae_eq_condExpL1 hm f).mono fun x hx _ => hx)]
  exact setIntegral_condExpL1 hf hs
/-
**MeasureTheory.integral_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_condExp (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] : ∫ x, (μ[
f | m]) x ∂μ = ∫ x, f x ∂μ
参数：hm : m <= m₀；μ.trim hm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_condExp (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] :
    ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ := by
  by_cases hf : Integrable f μ
  · suffices ∫ x in Set.univ, (μ[f | m]) x ∂μ = ∫ x in Set.univ, f x ∂μ by
      simp_rw [setIntegral_univ] at this; exact this
    exact setIntegral_condExp hm hf .univ
  simp only [condExp_of_not_integrable hf, Pi.zero_apply, integral_zero, integral_undef hf]

/-- **Law of total probability** using `condExp` as conditional probability. -/
/-
**MeasureTheory.integral_condExp_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integral_condExp_indicator [mβ : MeasurableSpace β] {Y : α -> β} (hY : Mea
surable Y) [SigmaFinite (μ.trim hY.comap_le)] {A : Set α} (hA : MeasurableSet A)
 : ∫ x, (μ[(A.indicator fun _ => (1 : Real)) | mβ.comap Y]) x ∂μ = μ.real A
参数：hY : Measurable Y；μ.trim hY.comap_le；hA : MeasurableSet A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_condExp`：integral_condExp (hm : m <= m₀) [hμm : S
igmaFinite (μ.trim hm)] : ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
**Law of total probability** using `condExp` as conditional probability.
-/
theorem integral_condExp_indicator [mβ : MeasurableSpace β] {Y : α → β} (hY : Measurable Y)
    [SigmaFinite (μ.trim hY.comap_le)] {A : Set α} (hA : MeasurableSet A) :
    ∫ x, (μ[(A.indicator fun _ ↦ (1 : ℝ)) | mβ.comap Y]) x ∂μ = μ.real A := by
  rw [integral_condExp, integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
/-
**MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：ae_eq_condExp_of_forall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim
 hm)] {f g : α -> E} (hf : Integrable f μ) (hg_int_finite : forall s, Measurable
Set[m] s -> μ s < ∞ -> IntegrableOn g s μ) (hg_eq : forall s : Set α, Measurable
Set[m] s -> μ s < ∞ -> ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ) (hgm : AEStronglyMea
surable[m] g μ) : g =ᵐ[μ] μ[f | m]
参数：hm : m <= m₀；μ.trim hm；hf : Integrable f μ；hg_int_finite : forall s, Measurab
leSet[m] s -> μ s < ∞ -> IntegrableOn g s μ；hg_eq : forall s : Set α, Measurable
Set[m] s -> μ s < ∞ -> ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ；hgm : AEStronglyMeasu
rable[m] g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'`：ae_eq_of_f
orall_setIntegral_eq_of_sigmaFinite' (hm : m <= m0) [SigmaFinite (μ.trim hm)] {f
 g : α -> F'} (hf_int_finite : forall s, Measurabl…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])

--- 原说明 ---
**Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and ha
s same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`.
-/
theorem ae_eq_condExp_of_forall_setIntegral_eq (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f g : α → E} (hf : Integrable f μ)
    (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable[m] g μ) : g =ᵐ[μ] μ[f | m] := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm hg_int_finite
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs hμs => ?_) hgm
    (StronglyMeasurable.aestronglyMeasurable stronglyMeasurable_condExp)
  rw [hg_eq s hs hμs, setIntegral_condExp hm hf hs]
/-
**MeasureTheory.condExp_bot'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_bot' [hμ : NeZero μ] (f : α -> E) : μ[f | ⊥] = fun _ => (μ.real Se
t.univ)⁻¹ • ∫ x, f x ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `stronglyMeasurable_bot_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
[inst : TopologicalSpace β] [Nonempty β] [T2Space β],   MeasureTheory.StronglyMe
asurable f ↔ ∃ c…
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_condExp`：integral_condExp (hm : m <= m₀) [hμm : S
igmaFinite (μ.trim hm)] : ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_eq_zero_iff`：toReal_eq_zero_iff (x : Real>=0∞) : x.toReal
 = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `MeasureTheory.Measure.instNeZeroENNRealCoeSetUniv`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [NeZero μ], NeZero (μ Set.uni
v)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.sigmaFinite_trim_bot_iff`：sigmaFinite_trim_bot_iff : Sigma
Finite (μ.trim bot_le) ↔ IsFiniteMeasure μ
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.not_isFiniteMeasure_iff`：not_isFiniteMeasure_iff : ¬IsFini
teMeasure μ ↔ μ univ = ∞
（共 32 条，此处仅展示前 30 条）
-/
theorem condExp_bot' [hμ : NeZero μ] (f : α → E) :
    μ[f | ⊥] = fun _ => (μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ := by
  by_cases hμ_finite : IsFiniteMeasure μ
  swap
  · have h : ¬SigmaFinite (μ.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hμ_finite
    rw [condExp_of_not_sigmaFinite bot_le h]
    simp only [hμ_finite, ENNReal.toReal_top, inv_zero, zero_smul, measureReal_def]
    rfl
  have h_meas : StronglyMeasurable[⊥] (μ[f | ⊥]) := stronglyMeasurable_condExp
  obtain ⟨c, h_eq⟩ := stronglyMeasurable_bot_iff.mp h_meas
  rw [h_eq]
  have h_integral : ∫ x, (μ[f | ⊥]) x ∂μ = ∫ x, f x ∂μ := integral_condExp bot_le
  simp_rw [h_eq, integral_const] at h_integral
  rw [← h_integral, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀, one_smul]
  rw [Ne, measureReal_def, ENNReal.toReal_eq_zero_iff, not_or]
  exact ⟨NeZero.ne _, measure_ne_top μ Set.univ⟩
/-
**MeasureTheory.condExp_bot_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_bot_ae_eq (f : α -> E) : μ[f | ⊥] =ᵐ[μ] fun _ => (μ.real Set.univ)
⁻¹ • ∫ x, f x ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Filter.eventually_bot`：eventually_bot {p : α -> Prop} : forallᶠ x in ⊥, 
p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_bot'`：condExp_bot' [hμ : NeZero μ] (f : α -> E) : 
μ[f | ⊥] = fun _ => (μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ
-/
theorem condExp_bot_ae_eq (f : α → E) :
    μ[f | ⊥] =ᵐ[μ] fun _ => (μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rw [ae_zero]; exact eventually_bot
  · exact Eventually.of_forall <| congr_fun (condExp_bot' f)

@[simp]
/-
**MeasureTheory.condExp_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_bot [IsProbabilityMeasure μ] (f : α -> E) : μ[f | ⊥] = fun _ => ∫ 
x, f x ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.condExp_bot'`：condExp_bot' [hμ : NeZero μ] (f : α -> E) : 
μ[f | ⊥] = fun _ => (μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem condExp_bot [IsProbabilityMeasure μ] (f : α → E) : μ[f | ⊥] = fun _ => ∫ x, f x ∂μ := by
  refine (condExp_bot' f).trans ?_
  rw [probReal_univ, inv_one, one_smul]
/-
**MeasureTheory.condExp_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_add (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpa
ce α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
参数：hf : Integrable f μ；hg : Integrable g μ；m : MeasurableSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_ae_eq_condExpL1`：condExp_ae_eq_condExpL1 [Complete
Space E] (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) : μ[f | m] 
=ᵐ[μ] condExpL1 hm μ f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpL1_add`：condExpL1_add (hf : Integrable f μ) (hg : I
ntegrable g μ) : condExpL1 hm μ (f + g) = condExpL1 hm μ f + condExpL1 hm μ g
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
theorem condExp_add (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpace α) :
    μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_add hf hg]
  exact (coeFn_add _ _).trans
    ((condExp_ae_eq_condExpL1 hm _).symm.add (condExp_ae_eq_condExpL1 hm _).symm)
/-
**MeasureTheory.condExp_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_finsetSum {ι : Type*} {s : Finset ι} {f : ι -> α -> E} (hf : foral
l i in s, Integrable (f i) μ) (m : MeasurableSpace α) : μ[∑ i in s, f i | m] =ᵐ[
μ] ∑ i in s, μ[f i | m]
参数：hf : forall i in s, Integrable (f i) μ；m : MeasurableSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `MeasureTheory.condExp_zero`：condExp_zero : μ[(0 : α -> E) | m] = 0
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_add`：condExp_add (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `MeasureTheory.integrable_finsetSum'`：integrable_finsetSum' {ι} (s : Fins
et ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (
∑ i in s, f i) μ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Finset.forall_of_forall_insert`：forall_of_forall_insert {p : α -> Prop} 
{a : α} {s : Finset α} (H : forall x, x in insert a s -> p x) (x) (h : x in s) :
 p x
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
-/
theorem condExp_finsetSum {ι : Type*} {s : Finset ι} {f : ι → α → E}
    (hf : ∀ i ∈ s, Integrable (f i) μ) (m : MeasurableSpace α) :
    μ[∑ i ∈ s, f i | m] =ᵐ[μ] ∑ i ∈ s, μ[f i | m] := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, condExp_zero]
  | insert i s his heq =>
    rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (condExp_add (hf i <| Finset.mem_insert_self i s)
      (integrable_finsetSum' _ <| Finset.forall_of_forall_insert hf) _).trans
        ((EventuallyEq.refl _ _).add <| heq <| Finset.forall_of_forall_insert hf)

@[deprecated (since := "2026-04-08")] alias condExp_finset_sum := condExp_finsetSum
/-
**MeasureTheory.condExp_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : α -> E) (m : MeasurableSpace α
) : μ[c • f | m] =ᵐ[μ] c • μ[f | m]
参数：c : 𝕜；f : α -> E；m : MeasurableSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_ae_eq_condExpL1`：condExp_ae_eq_condExpL1 [Complete
Space E] (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) : μ[f | m] 
=ᵐ[μ] condExpL1 hm μ f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpL1_smul`：condExpL1_smul (c : 𝕜) (f : α -> F') : con
dExpL1 hm μ (c • f) = c • condExpL1 hm μ f
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
theorem condExp_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : α → E) (m : MeasurableSpace α) :
    μ[c • f | m] =ᵐ[μ] c • μ[f | m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_smul c f]
  refine (condExp_ae_eq_condExpL1 hm f).mp ?_
  refine (coeFn_smul c (condExpL1 hm μ f)).mono fun x hx1 hx2 => ?_
  simp only [hx1, hx2, Pi.smul_apply]
/-
**MeasureTheory.condExp_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_neg (f : α -> E) (m : MeasurableSpace α) : μ[-f | m] =ᵐ[μ] -μ[f | 
m]
参数：f : α -> E；m : MeasurableSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `MeasureTheory.condExp_smul`：condExp_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : 
α -> E) (m : MeasurableSpace α) : μ[c • f | m] =ᵐ[μ] c • μ[f | m]
-/
theorem condExp_neg (f : α → E) (m : MeasurableSpace α) : μ[-f | m] =ᵐ[μ] -μ[f | m] := by
  calc
    μ[-f | m] = μ[(-1 : ℝ) • f | m] := by rw [neg_one_smul ℝ f]
    _ =ᵐ[μ] (-1 : ℝ) • μ[f | m] := condExp_smul ..
    _ = -μ[f | m] := neg_one_smul ℝ (μ[f | m])
/-
**MeasureTheory.condExp_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_sub (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpa
ce α) : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m]
参数：hf : Integrable f μ；hg : Integrable g μ；m : MeasurableSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_add`：condExp_add (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
-/
theorem condExp_sub (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpace α) :
    μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m] := by
  simp_rw [sub_eq_add_neg]
  exact (condExp_add hf hg.neg _).trans (EventuallyEq.rfl.add (condExp_neg ..))

/-- **Tower property of the conditional expectation**.

Taking the `m₂`-conditional expectation then the `m₁`-conditional expectation, where `m₁` is a
smaller σ-algebra, is the same as taking the `m₁`-conditional expectation directly. -/
/-
**MeasureTheory.condExp_condExp_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_condExp_of_le {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α} (hm₁₂
 : m₁ <= m₂) (hm₂ : m₂ <= m₀) [SigmaFinite (μ.trim hm₂)] : μ[μ[f | m₂] | m₁] =ᵐ[
μ] μ[f | m₁]
参数：hm₁₂ : m₁ <= m₂；hm₂ : m₂ <= m₀；μ.trim hm₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'`：ae_eq_of_f
orall_setIntegral_eq_of_sigmaFinite' (hm : m <= m0) [SigmaFinite (μ.trim hm)] {f
 g : α -> F'} (hf_int_finite : forall s, Measurabl…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.condExp_zero`：condExp_zero : μ[(0 : α -> E) | m] = 0
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0

--- 原说明 ---
**Tower property of the conditional expectation**.

Taking the `m₂`-conditional expectation then the `m₁`-conditional expectation, w
here `m₁` is a
smaller σ-algebra, is the same as taking the `m₁`-conditional expectation direct
ly.
-/
theorem condExp_condExp_of_le {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ ≤ m₂)
    (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)] : μ[μ[f | m₂] | m₁] =ᵐ[μ] μ[f | m₁] := by
  by_cases hμm₁ : SigmaFinite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [condExp_of_not_sigmaFinite (hm₁₂.trans hm₂) hμm₁]; rfl
  by_cases hf : Integrable f μ
  swap; · simp_rw [condExp_of_not_integrable hf, condExp_zero]; rfl
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm₁₂.trans hm₂)
    (fun s _ _ => integrable_condExp.integrableOn) (fun s _ _ => integrable_condExp.integrableOn) ?_
    stronglyMeasurable_condExp.aestronglyMeasurable
    stronglyMeasurable_condExp.aestronglyMeasurable
  intro s hs _
  rw [setIntegral_condExp (hm₁₂.trans hm₂) integrable_condExp hs]
  rw [setIntegral_condExp (hm₁₂.trans hm₂) hf hs, setIntegral_condExp hm₂ hf (hm₁₂ s hs)]

/-- Conditional expectation commutes with continuous linear maps. -/
/-
**MeasureTheory._root_.ContinuousLinearMap.comp_condExp_comm** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditional expectation commutes with continuous linear maps.
-/
theorem _root_.ContinuousLinearMap.comp_condExp_comm {F : Type*} [NormedAddCommGroup F]
    [CompleteSpace F] [NormedSpace ℝ F] (hf_int : Integrable f μ) (T : E →L[ℝ] F) :
    T ∘ μ[f | m] =ᵐ[μ] μ[T ∘ f | m] := by
  by_cases hm : m ≤ m₀
  · by_cases hμ : SigmaFinite (μ.trim hm)
    · refine ae_eq_condExp_of_forall_setIntegral_eq hm ?_ (fun s ms hs => ?_) (fun s ms hs => ?_) ?_
      · exact T.integrable_comp hf_int
      · exact (T.integrable_comp integrable_condExp).integrableOn
      · calc
          ∫ x in s, (T ∘ μ[f | m]) x ∂μ = T (∫ x in s, μ[f | m] x ∂μ) :=
            T.integral_comp_comm integrable_condExp.restrict
          _ = T (∫ x in s, f x ∂μ) := congrArg T (setIntegral_condExp hm hf_int ms)
          _ = ∫ x in s, (T ∘ f) x ∂μ := (T.integral_comp_comm hf_int.restrict).symm
      · exact T.cont.comp_aestronglyMeasurable stronglyMeasurable_condExp.aestronglyMeasurable
    · simp [condExp_of_not_sigmaFinite hm hμ]
  · simp [condExp_of_not_le hm]

/-- Conditional expectation commutes with affine functions. Note that `IsFiniteMeasure μ` is a
necessary assumption because we want constant functions to be integrable. -/
/-
**MeasureTheory._root_.ContinuousLinearMap.comp_condExp_add_const_comm** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditional expectation commutes with affine functions. Note that `IsFiniteMeasu
re μ` is a
necessary assumption because we want constant functions to be integrable.
-/
theorem _root_.ContinuousLinearMap.comp_condExp_add_const_comm {F : Type*} [NormedAddCommGroup F]
    [CompleteSpace F] [NormedSpace ℝ F] [IsFiniteMeasure μ] (hm : m ≤ m₀) (hf_int : Integrable f μ)
    (T : E →L[ℝ] F) (a : F) : (fun x ↦ T (μ[f | m] x) + a) =ᵐ[μ] μ[fun y ↦ T (f y) + a | m] := by
  have hp : (fun x ↦ T (μ[f | m] x) + a) =ᵐ[μ] μ[T ∘ f | m] + μ[(fun y ↦ a) | m] := by
    filter_upwards [T.comp_condExp_comm hf_int] with b hb
    simpa [condExp_const hm a]
  exact hp.trans (condExp_add (T.integrable_comp hf_int) (integrable_const a) m).symm

section RCLike

variable [InnerProductSpace 𝕜 E]

/-
**MeasureTheory.MemLp.condExpL2_ae_eq_condExp'** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {𝕜 : Type u_4} [inst : RCLike 𝕜] {m m₀ : M
easurableSpace α}   {μ : MeasureTheory.Measure α} {f : α → E} [inst_1 : NormedAd
dCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 : CompleteSpace E] [inst_4 : 
InnerProductSpace 𝕜 E] (hm : m ≤ m₀),   MeasureTheory.Integrable f μ →     ∀ (hf
2 : MeasureTheory.MemLp f 2 μ) [MeasureTheory.SigmaFinite (μ.trim hm)],       ↑↑
↑((MeasureTheory.condExpL2 E 𝕜 hm) (MeasureTheory.MemLp.toLp f hf2)) =ᵐ[μ] μ[f |
 m]
参数：hm : m ≤ m₀；hf2 : MeasureTheory.MemLp f 2 μ；μ.trim hm；(MeasureTheory.condExpL
2 E 𝕜 hm) (MeasureTheory.MemLp.toLp f hf2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.integrableOn_condExpL2_of_measure_ne_top`：integrableOn_con
dExpL2_of_measure_ne_top (hm : m <= m0) (hμs : μ s != ∞) (f : α ->₂[μ] E) : Inte
grableOn (ε
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_condExpL2_eq`：integral_condExpL2_eq (hm : m <= m0
) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s) (hμs : μ s != ∞) : ∫ x in s, (condEx
pL2 E' 𝕜 hm f : α -> E') …
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL2`：aestronglyMeasurable_condE
xpL2 (hm : m <= m0) (f : α ->₂[μ] E) : AEStronglyMeasurable[m] (condExpL2 E 𝕜 hm
 f : α -> E) μ
-/
lemma MemLp.condExpL2_ae_eq_condExp' (hm : m ≤ m₀) (hf1 : Integrable f μ) (hf2 : MemLp f 2 μ)
    [SigmaFinite (μ.trim hm)] : condExpL2 E 𝕜 hm hf2.toLp =ᵐ[μ] μ[f | m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf1
    (fun s hs htop ↦ integrableOn_condExpL2_of_measure_ne_top hm htop.ne _) (fun s hs htop ↦ ?_)
    (aestronglyMeasurable_condExpL2 hm _)
  rw [integral_condExpL2_eq hm (hf2.toLp _) hs htop.ne]
  refine setIntegral_congr_ae (hm _ hs) ?_
  filter_upwards [hf2.coeFn_toLp] with ω hω _ using hω
/-
**MeasureTheory.MemLp.condExpL2_ae_eq_condExp** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {𝕜 : Type u_4} [inst : RCLike 𝕜] {m m₀ : M
easurableSpace α}   {μ : MeasureTheory.Measure α} {f : α → E} [inst_1 : NormedAd
dCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 : CompleteSpace E] [inst_4 : 
InnerProductSpace 𝕜 E] (hm : m ≤ m₀) (hf : MeasureTheory.MemLp f 2 μ)   [Measure
Theory.IsFiniteMeasure μ],   ↑↑↑((MeasureTheory.condExpL2 E 𝕜 hm) (MeasureTheory
.MemLp.toLp f hf)) =ᵐ[μ] μ[f | m]
参数：hm : m ≤ m₀；hf : MeasureTheory.MemLp f 2 μ；(MeasureTheory.condExpL2 E 𝕜 hm) (
MeasureTheory.MemLp.toLp f hf)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.MemLp.condExpL2_ae_eq_condExp'`：∀ {α : Type u_1} {E : Type
 u_3} {𝕜 : Type u_4} [inst : RCLike 𝕜] {m m₀ : MeasurableSpace α}   {μ : Measure
Theory.Measure α} {f : α → E} [ins…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
lemma MemLp.condExpL2_ae_eq_condExp (hm : m ≤ m₀) (hf : MemLp f 2 μ) [IsFiniteMeasure μ] :
    condExpL2 E 𝕜 hm hf.toLp =ᵐ[μ] μ[f | m] :=
  hf.condExpL2_ae_eq_condExp' hm (memLp_one_iff_integrable.1 <| hf.mono_exponent one_le_two)

end RCLike

end NormedSpace

end NormedAddCommGroup

section NormedRing
variable {R : Type*} [NormedRing R] [NormedSpace ℝ R] [CompleteSpace R]

@[simp]
/-
**MeasureTheory.condExp_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_ofNat (n : Nat) [n.AtLeastTwo] (f : α -> R) : μ[ofNat(n) * f | m] 
=ᵐ[μ] ofNat(n) * μ[f | m]
参数：n : Nat；f : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `MeasureTheory.condExp_smul`：condExp_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : 
α -> E) (m : MeasurableSpace α) : μ[c • f | m] =ᵐ[μ] c • μ[f | m]
-/
lemma condExp_ofNat (n : ℕ) [n.AtLeastTwo] (f : α → R) :
    μ[ofNat(n) * f | m] =ᵐ[μ] ofNat(n) * μ[f | m] := by
  simpa [Nat.cast_smul_eq_nsmul] using! condExp_smul (μ := μ) (m := m) (n : ℝ) f

end NormedRing

section NormedLatticeAddCommGroup
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lebesgue dominated convergence theorem**: sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `condExpL1`. -/
/-
**MeasureTheory.tendsto_condExpL1_of_dominated_convergence** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：tendsto_condExpL1_of_dominated_convergence (hm : m <= m₀) [SigmaFinite (μ.
trim hm)] {fs : Nat -> α -> E} {f : α -> E} (bound_fs : α -> Real) (hfs_meas : f
orall n, AEStronglyMeasurable (fs n) μ) (h_int_bound_fs : Integrable bound_fs μ)
 (hfs_bound : forall n, forallᵐ x ∂μ, ‖fs n x‖ <= bound_fs x) (hfs : forallᵐ x ∂
μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) : Tendsto (fun n => condExpL1 hm μ
 (fs n)) atTop (𝓝 (condExpL1 hm μ f))
参数：hm : m <= m₀；μ.trim hm；bound_fs : α -> Real；hfs_meas : forall n, AEStronglyMe
asurable (fs n) μ；h_int_bound_fs : Integrable bound_fs μ；hfs_bound : forall n, f
orallᵐ x ∂μ, ‖fs n x‖ <= bound_fs x；hfs : forallᵐ x ∂μ, Tendsto (fun n => fs n x
) atTop (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendsto_setToFun_of_dominated_convergence`：tendsto_setToFu
n_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {fs : Nat -> α 
-> E} {f : α -> E} (bound : α -> Real) (fs_me…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…

--- 原说明 ---
**Lebesgue dominated convergence theorem**: sufficient conditions under which al
most
  everywhere convergence of a sequence of functions implies the convergence of t
heir image by
  `condExpL1`.
-/
theorem tendsto_condExpL1_of_dominated_convergence (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {fs : ℕ → α → E} {f : α → E} (bound_fs : α → ℝ)
    (hfs_meas : ∀ n, AEStronglyMeasurable (fs n) μ) (h_int_bound_fs : Integrable bound_fs μ)
    (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
    (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => condExpL1 hm μ (fs n)) atTop (𝓝 (condExpL1 hm μ f)) :=
  tendsto_setToFun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs
/-
**MeasureTheory.condExp_tsum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_tsum [CompleteSpace E] {ι : Type*} [Countable ι] {f : ι -> α -> E}
 (hf : forall i, AEStronglyMeasurable (f i) μ) (hf' : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ !=
 ∞) : μ[fun a => ∑' i, f i a | m] =ᵐ[μ] fun a => ∑' i, μ[f i | m] a
参数：hf : forall i, AEStronglyMeasurable (f i) μ；hf' : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ != 
∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.condExp_ae_eq_condExpL1`：condExp_ae_eq_condExpL1 [Complete
Space E] (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) : μ[f | m] 
=ᵐ[μ] condExpL1 hm μ f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_condExpInd`：dominatedFinMeasAddit
ive_condExpInd (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : Domina
tedFinMeasAdditive μ (condExpInd G hm μ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.enorm_setToFun_le`：enorm_setToFun_le (hT : DominatedFinMea
sAdditive μ T C) (hC : 0 <= C) : ‖setToFun μ T hT f‖ₑ <= NNReal.mk C hC * ∫⁻ x, 
‖f x‖ₑ ∂μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.Lp.coeFn_tsum`：coeFn_tsum {ι : Type*} [Countable ι] {p : R
eal>=0∞} [hp : Fact (1 <= p)] [CompleteSpace E] {f : ι -> Lp E p μ} (hf : ∑' n, 
‖f n‖ₑ != ∞) : ⇑(…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 43 条，此处仅展示前 30 条）
-/
theorem condExp_tsum [CompleteSpace E]
    {ι : Type*} [Countable ι] {f : ι → α → E} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ∞) :
    μ[fun a ↦ ∑' i, f i a | m] =ᵐ[μ] fun a ↦ ∑' i, μ[f i | m] a := by
  by_cases hm : m ≤ m₀; swap
  · simp only [condExp_of_not_le hm, Pi.zero_apply, tsum_zero]
    exact ae_eq_rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap
  · simp only [condExp_of_not_sigmaFinite hm hμm, Pi.zero_apply, tsum_zero]
    exact ae_eq_rfl
  grw [condExp_ae_eq_condExpL1 hm]
  have A : ∀ᵐ a ∂μ, ∀ i, μ[f i | m] a = condExpL1 hm μ (f i) a :=
    ae_all_iff.2 (fun i ↦ condExp_ae_eq_condExpL1 hm _)
  have B : ∑' (n : ι), ‖condExpL1 hm μ (f n)‖ₑ ≠ ∞ := by
    apply (lt_of_le_of_lt ?_ hf'.lt_top).ne
    gcongr with i
    exact (enorm_setToFun_le _ (by simp)).trans_eq (by simp)
  have C := coeFn_tsum (f := fun i ↦ condExpL1 hm μ (f i)) B
  filter_upwards [A, C] with a ha h'a
  simp_all [condExpL1, setToFun_tsum]

variable [CompleteSpace E]

/-- If two sequences of functions have a.e. equal conditional expectations at each step, converge
and verify dominated convergence hypotheses, then the conditional expectations of their limits are
a.e. equal. -/
/-
**MeasureTheory.tendsto_condExp_unique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：tendsto_condExp_unique (fs gs : Nat -> α -> E) (f g : α -> E) (hfs_int : f
orall n, Integrable (fs n) μ) (hgs_int : forall n, Integrable (gs n) μ) (hfs : f
orallᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) (hgs : forallᵐ x ∂μ, Ten
dsto (fun n => gs n x) atTop (𝓝 (g x))) (bound_fs : α -> Real) (h_int_bound_fs :
 Integrable bound_fs μ) (bound_gs : α -> Real) (h_int_bound_gs : Integrable boun
d_gs μ) (hfs_bound : forall n, forallᵐ x ∂μ, ‖fs n x‖ <= bound_fs x) (hgs_bound 
: forall n, forallᵐ x ∂μ, 
参数：fs gs : Nat -> α -> E；f g : α -> E；hfs_int : forall n, Integrable (fs n) μ；hg
s_int : forall n, Integrable (gs n) μ；hfs : forallᵐ x ∂μ, Tendsto (fun n => fs n
 x) atTop (𝓝 (f x))；hgs : forallᵐ x ∂μ, Tendsto (fun n => gs n x) atTop (𝓝 (g x)
)；bound_fs : α -> Real；h_int_bound_fs : Integrable bound_fs μ；bound_gs : α -> Re
al；h_int_bound_gs : Integrable bound_gs μ；hfs_bound : forall n, forallᵐ x ∂μ, ‖f
s n x‖ <= bound_fs x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_ae_eq_condExpL1`：condExp_ae_eq_condExpL1 [Complete
Space E] (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) : μ[f | m] 
=ᵐ[μ] condExpL1 hm μ f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.ext_iff`：∀ {α : Type u_1} {E : Type u_4} {m : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f g : ↥…
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.tendsto_condExpL1_of_dominated_convergence`：tendsto_condEx
pL1_of_dominated_convergence (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {fs : Nat 
-> α -> E} {f : α -> E} (bound_fs : α -> Real)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `tendsto_nhds_unique_of_eventuallyEq`：tendsto_nhds_unique_of_eventuallyEq
 [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l
 (𝓝 a)) (hb : Tendsto g l…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0

--- 原说明 ---
If two sequences of functions have a.e. equal conditional expectations at each s
tep, converge
and verify dominated convergence hypotheses, then the conditional expectations o
f their limits are
a.e. equal.
-/
theorem tendsto_condExp_unique (fs gs : ℕ → α → E) (f g : α → E)
    (hfs_int : ∀ n, Integrable (fs n) μ) (hgs_int : ∀ n, Integrable (gs n) μ)
    (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hgs : ∀ᵐ x ∂μ, Tendsto (fun n => gs n x) atTop (𝓝 (g x))) (bound_fs : α → ℝ)
    (h_int_bound_fs : Integrable bound_fs μ) (bound_gs : α → ℝ)
    (h_int_bound_gs : Integrable bound_gs μ) (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
    (hgs_bound : ∀ n, ∀ᵐ x ∂μ, ‖gs n x‖ ≤ bound_gs x) (hfg : ∀ n, μ[fs n | m] =ᵐ[μ] μ[gs n | m]) :
    μ[f | m] =ᵐ[μ] μ[g | m] := by
  by_cases hm : m ≤ m₀; swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  refine (condExp_ae_eq_condExpL1 hm f).trans ((condExp_ae_eq_condExpL1 hm g).trans ?_).symm
  rw [← Lp.ext_iff]
  have hn_eq : ∀ n, condExpL1 hm μ (gs n) = condExpL1 hm μ (fs n) := by
    intro n
    ext1
    refine (condExp_ae_eq_condExpL1 hm (gs n)).symm.trans ((hfg n).symm.trans ?_)
    exact condExp_ae_eq_condExpL1 hm (fs n)
  have hcond_fs : Tendsto (fun n => condExpL1 hm μ (fs n)) atTop (𝓝 (condExpL1 hm μ f)) :=
    tendsto_condExpL1_of_dominated_convergence hm _ (fun n => (hfs_int n).1) h_int_bound_fs
      hfs_bound hfs
  have hcond_gs : Tendsto (fun n => condExpL1 hm μ (gs n)) atTop (𝓝 (condExpL1 hm μ g)) :=
    tendsto_condExpL1_of_dominated_convergence hm _ (fun n => (hgs_int n).1) h_int_bound_gs
      hgs_bound hgs
  exact tendsto_nhds_unique_of_eventuallyEq hcond_gs hcond_fs (Eventually.of_forall hn_eq)

variable [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
/-
**MeasureTheory.condExp_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_mono (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f <=ᵐ[μ] g
) : μ[f | m] <=ᵐ[μ] μ[g | m]
参数：hf : Integrable f μ；hg : Integrable g μ；hfg : f <=ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.trans_le`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f =ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_ae_eq_condExpL1`：condExp_ae_eq_condExpL1 [Complete
Space E] (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) : μ[f | m] 
=ᵐ[μ] condExpL1 hm μ f
· 使用定理 `Filter.EventuallyLE.trans_eq`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g =ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `MeasureTheory.condExpL1_mono`：condExpL1_mono {E} [NormedAddCommGroup E] 
[PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E] [NormedSpace Real 
E] [IsOrderedModul…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `Filter.EventuallyLE.refl`：∀ {α : Type u} {β : Type v} [inst : Preorder β
] (l : Filter α) (f : α → β), f ≤ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
lemma condExp_mono (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    μ[f | m] ≤ᵐ[μ] μ[g | m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm _).trans_le
    ((condExpL1_mono hf hg hfg).trans_eq (condExp_ae_eq_condExpL1 hm _).symm)
/-
**MeasureTheory.condExp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_nonneg (hf : 0 <=ᵐ[μ] f) : 0 <=ᵐ[μ] μ[f | m]
参数：hf : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.condExp_zero`：condExp_zero : μ[(0 : α -> E) | m] = 0
· 使用引理 `MeasureTheory.condExp_mono`：condExp_mono (hf : Integrable f μ) (hg : Int
egrable g μ) (hfg : f <=ᵐ[μ] g) : μ[f | m] <=ᵐ[μ] μ[g | m]
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `Filter.EventuallyLE.refl`：∀ {α : Type u} {β : Type v} [inst : Preorder β
] (l : Filter α) (f : α → β), f ≤ᶠ[l] f
-/
lemma condExp_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] μ[f | m] := by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α → E) = μ[0 | m])]
    exact condExp_mono (integrable_zero _ _ _) hfint hf
  · rw [condExp_of_not_integrable hfint]
/-
**MeasureTheory.condExp_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_nonpos (hf : f <=ᵐ[μ] 0) : μ[f | m] <=ᵐ[μ] 0
参数：hf : f <=ᵐ[μ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.condExp_zero`：condExp_zero : μ[(0 : α -> E) | m] = 0
· 使用引理 `MeasureTheory.condExp_mono`：condExp_mono (hf : Integrable f μ) (hg : Int
egrable g μ) (hfg : f <=ᵐ[μ] g) : μ[f | m] <=ᵐ[μ] μ[g | m]
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `Filter.EventuallyLE.refl`：∀ {α : Type u} {β : Type v} [inst : Preorder β
] (l : Filter α) (f : α → β), f ≤ᶠ[l] f
-/
lemma condExp_nonpos (hf : f ≤ᵐ[μ] 0) : μ[f | m] ≤ᵐ[μ] 0 := by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α → E) = μ[0 | m])]
    exact condExp_mono hfint (integrable_zero _ _ _) hf
  · rw [condExp_of_not_integrable hfint]

end NormedLatticeAddCommGroup
end MeasureTheory

