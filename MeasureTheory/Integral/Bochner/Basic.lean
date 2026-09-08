/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.L1

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here using
the L1 Bochner integral constructed in the file `Mathlib/MeasureTheory/Integral/Bochner/L1.lean`.

## Main definitions

The Bochner integral is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

* `MeasureTheory.integral`: the Bochner integral on functions defined as the Bochner integral of
  its equivalence class in L1 space, if it is in L1, and 0 otherwise.

The result of that construction is `∫ a, f a ∂μ`, which is definitionally equal to
`setToFun (dominatedFinMeasAdditive_weightedSMul μ) f`. Some basic properties of the integral
(like linearity) are particular cases of the properties of `setToFun` (which are described in the
file `Mathlib/MeasureTheory/Integral/SetToL1.lean`).

## Main statements

1. Basic properties of the Bochner integral on functions of type `α → E`, where `α` is a measure
   space and `E` is a real normed space.

  * `integral_zero`                  : `∫ 0 ∂μ = 0`
  * `integral_add`                   : `∫ x, f x + g x ∂μ = ∫ x, f ∂μ + ∫ x, g x ∂μ`
  * `integral_neg`                   : `∫ x, - f x ∂μ = - ∫ x, f x ∂μ`
  * `integral_sub`                   : `∫ x, f x - g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ`
  * `integral_smul`                  : `∫ x, r • f x ∂μ = r • ∫ x, f x ∂μ`
  * `integral_congr_ae`              : `f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ`
  * `norm_integral_le_integral_norm` : `‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ`

2. Basic order properties of the Bochner integral on functions of type `α → E`, where `α` is a
   measure space and `E` is a real ordered Banach space.

  * `integral_nonneg_of_ae` : `0 ≤ᵐ[μ] f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos_of_ae` : `f ≤ᵐ[μ] 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono_ae`      : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`
  * `integral_nonneg`       : `0 ≤ f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos`       : `f ≤ 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono`         : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`

3. Propositions connecting the Bochner integral with the integral on `ℝ≥0∞`-valued functions,
   which is called `lintegral` and has the notation `∫⁻`.

  * `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` :
    `∫ x, f x ∂μ = ∫⁻ x, f⁺ x ∂μ - ∫⁻ x, f⁻ x ∂μ`,
    where `f⁺` is the positive part of `f` and `f⁻` is the negative part of `f`.
  * `integral_eq_lintegral_of_nonneg_ae`          : `0 ≤ᵐ[μ] f → ∫ x, f x ∂μ = ∫⁻ x, f x ∂μ`

4. (In the file `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`)
  `tendsto_integral_of_dominated_convergence` : the Lebesgue dominated convergence theorem

5. (In `Mathlib/MeasureTheory/Integral/Bochner/Set.lean`) integration commutes with continuous
  linear maps.

  * `ContinuousLinearMap.integral_comp_comm`
  * `LinearIsometry.integral_comp_comm`

## Notes

Some tips on how to prove a proposition if the API for the Bochner integral is not enough so that
you need to unfold the definition of the Bochner integral and go back to simple functions.

One method is to use the theorem `Integrable.induction` in the file
`Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean` (or one of the related results, like
`Lp.induction` for functions in `Lp`), which allows you to prove something for an arbitrary
integrable function.

Another method is using the following steps.
See `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` for a complicated example, which proves
that `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, with the first integral sign being the Bochner integral of a real-valued
function `f : α → ℝ`, and the second and third integral signs being integrals on `ℝ≥0∞`-valued
functions (called `lintegral`). The proof of `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`
is scattered in sections with the name `posPart`.

Here are the usual steps of proving that a property `p`, say `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, holds for all
functions :

1. First go to the `L¹` space.

   For example, if you see `ENNReal.toReal (∫⁻ a, ENNReal.ofReal <| ‖f a‖)`, that is the norm of
   `f` in `L¹` space. Rewrite using `L1.norm_of_fun_eq_lintegral_norm`.

2. Show that the set `{f ∈ L¹ | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}` is closed in `L¹` using `isClosed_eq`.

3. Show that the property holds for all simple functions `s` in `L¹` space.

   Typically, you need to convert various notions to their `SimpleFunc` counterpart, using lemmas
   like `L1.integral_coe_eq_integral`.

4. Since simple functions are dense in `L¹`,
   ```
   univ = closure {s simple}
        = closure {s simple | ∫ s = ∫⁻ s⁺ - ∫⁻ s⁻} : the property holds for all simple functions
        ⊆ closure {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}
        = {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻} : closure of a closed set is itself
   ```
   Use `isClosed_property` or `DenseRange.induction_on` for this argument.

## Notation

* `α →ₛ E` : simple functions (defined in `Mathlib/MeasureTheory/Function/SimpleFunc.lean`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
  `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
* `∫ a, f a ∂μ` : integral of `f` with respect to a measure `μ`
* `∫ a, f a` : integral of `f` with respect to `volume`, the default measure on the ambient type

We also define notations for integral on a set, which are described in the file
`Mathlib/MeasureTheory/Integral/Bochner/Set.lean`.

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if the font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

@[expose] public section

noncomputable section

open Filter ENNReal EMetric Set TopologicalSpace Topology
open scoped NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α E F 𝕜 : Type*}

local infixr:25 " →ₛ " => SimpleFunc

/-!
## The Bochner integral on functions

Define the Bochner integral on functions generally to be the `L1` Bochner integral, for integrable
functions, and 0 otherwise; prove its basic properties.
-/

variable [NormedAddCommGroup E] [NormedDivisionRing 𝕜]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open scoped Classical in
/-- The Bochner integral -/
irreducible_def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α → G) : G :=
  if _ : CompleteSpace G then
    if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0
  else 0

/-! In the notation for integrals, an expression like `∫ x, g ‖x‖ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫ x, f x = 0` will be parsed incorrectly. -/

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => integral μ r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)", "r:60:(scoped f => integral volume f) => r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => integral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => integral (Measure.restrict volume s) f) => r

section Properties

open ContinuousLinearMap MeasureTheory.SimpleFunc

variable [NormedSpace ℝ E]
variable {f : α → E} {m : MeasurableSpace α} {μ : Measure α}

section Basic

/-
**MeasureTheory.integral_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_eq [hE : CompleteSpace E] (f : α -> E) (hf : Integrable f μ) : ∫ 
a, f a ∂μ = L1.integral (hf.toL1 f)
参数：f : α -> E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq [hE : CompleteSpace E] (f : α → E) (hf : Integrable f μ) :
    ∫ a, f a ∂μ = L1.integral (hf.toL1 f) := by
  simp [integral, hE, hf]
/-
**MeasureTheory.integral_eq_setToFun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_eq_setToFun (f : α -> E) : ∫ a, f a ∂μ = setToFun μ (weightedSMul
 μ) (dominatedFinMeasAdditive_weightedSMul μ) f
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_setToFun (f : α → E) :
    ∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul μ) f := by
  by_cases hE : CompleteSpace E
  · simp only [integral, hE, ↓reduceDIte, L1.integral, setToFun]
    rfl
  · simp [integral, hE, setToFun]
/-
**MeasureTheory.L1.integral_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.L1`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} [inst_2 :
 CompleteSpace E] (f : ↥(MeasureTheory.Lp E 1 μ)),   MeasureTheory.L1.integral f
 = ∫ (a : α), ↑↑f a ∂μ
参数：f : ↥(MeasureTheory.Lp E 1 μ)；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.L1.setToFun_eq_setToL1`：∀ {α : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 
: NormedAddCommGroup F] [i…
-/
theorem L1.integral_eq_integral [CompleteSpace E] (f : α →₁[μ] E) :
    L1.integral f = ∫ a, f a ∂μ := by
  simp only [integral, L1.integral, integral_eq_setToFun]
  exact (L1.setToFun_eq_setToL1 (dominatedFinMeasAdditive_weightedSMul μ) f).symm
/-
**MeasureTheory.integral_undef** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_undef {f : α -> G} (h : ¬Integrable f μ) : ∫ a, f a ∂μ = 0
参数：h : ¬Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
-/
theorem integral_undef {f : α → G} (h : ¬Integrable f μ) : ∫ a, f a ∂μ = 0 := by
  simp only [integral_eq_setToFun]
  exact setToFun_undef (dominatedFinMeasAdditive_weightedSMul μ) h
/-
**MeasureTheory.Integrable.of_integral_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : No
rmedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {f : α → 
G}, ∫ (a : α), f a ∂μ ≠ 0 → MeasureTheory.Integrable f μ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
-/
theorem Integrable.of_integral_ne_zero {f : α → G} (h : ∫ a, f a ∂μ ≠ 0) : Integrable f μ :=
  Not.imp_symm integral_undef h
/-
**MeasureTheory.integral_non_aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integral_non_aestronglyMeasurable {f : α -> G} (h : ¬AEStronglyMeasurable 
f μ) : ∫ a, f a ∂μ = 0
参数：h : ¬AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
-/
theorem integral_non_aestronglyMeasurable {f : α → G} (h : ¬AEStronglyMeasurable f μ) :
    ∫ a, f a ∂μ = 0 :=
  integral_undef <| not_and_of_not_left _ h
/-
**MeasureTheory.integral_of_not_completeSpace** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_of_not_completeSpace {f : α -> G} (hG : ¬CompleteSpace G) : ∫ a, 
f a ∂μ = 0
参数：hG : ¬CompleteSpace G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_of_not_completeSpace {f : α → G} (hG : ¬CompleteSpace G) :
    ∫ a, f a ∂μ = 0 := by
  simp [integral, hG]

variable (α G)

@[simp]
/-
**MeasureTheory.integral_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_zero`：setToFun_zero (hT : DominatedFinMeasAdditiv
e μ T C) : setToFun μ T hT (0 : α -> E) = 0
-/
theorem integral_zero : ∫ _ : α, (0 : G) ∂μ = 0 := by
  simp only [integral_eq_setToFun]
  apply setToFun_zero

@[simp]
/-
**MeasureTheory.integral_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_zero' : integral μ (0 : α -> G) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
-/
theorem integral_zero' : integral μ (0 : α → G) = 0 :=
  integral_zero α G
/-
**MeasureTheory.integral_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_indicator (hs : MeasurableSet s) : ∫ x, indicator s f x ∂μ = ∫ x 
in s, f x ∂μ
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add_compl`：integral_add_compl (hs : MeasurableSet
 s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.IntegrableOn.integrable_indicator`：∀ {α : Type u_1} {ε' : 
Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [
inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `indicator_ae_eq_restrict`：indicator_ae_eq_restrict (hs : MeasurableSet s
) : indicator s f =ᵐ[μ.restrict s] f
· 使用定理 `indicator_ae_eq_restrict_compl`：indicator_ae_eq_restrict_compl (hs : Mea
surableSet s) : indicator s f =ᵐ[μ.restrict sᶜ] 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
-/
lemma integral_indicator₂ {β : Type*} (f : β → α → G) (s : Set β) (b : β) :
    ∫ y, s.indicator (f · y) b ∂μ = s.indicator (fun x ↦ ∫ y, f x y ∂μ) b := by
  by_cases hb : b ∈ s <;> simp [hb]

variable {α G}
/-
**MeasureTheory.integrable_of_integral_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integrable_of_integral_eq_one {f : α -> Real} (h : ∫ x, f x ∂μ = 1) : Inte
grable f μ
参数：h : ∫ x, f x ∂μ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.of_integral_ne_zero`：∀ {α : Type u_1} {G : Type
 u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSp
ace α}   {μ : MeasureTheory.Measur…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem integrable_of_integral_eq_one {f : α → ℝ} (h : ∫ x, f x ∂μ = 1) : Integrable f μ :=
  .of_integral_ne_zero <| h ▸ one_ne_zero
/-
**MeasureTheory.integral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_add {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) : 
∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_add`：setToFun_add (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f + g) = s
etToFun μ T hT f…
-/
theorem integral_add {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_add (dominatedFinMeasAdditive_weightedSMul μ) hf hg
/-
**MeasureTheory.integral_add'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_add' {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) :
 ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
-/
theorem integral_add' {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg
/-
**MeasureTheory.integral_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_finsetSum {ι} (s : Finset ι) {f : ι -> α -> G} (hf : forall i in 
s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i a ∂μ = ∑ i in s, ∫ a, f i a ∂μ
参数：s : Finset ι；hf : forall i in s, Integrable (f i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.setToFun_finsetSum`：setToFun_finsetSum (hT : DominatedFinM
easAdditive μ T C) {ι} (s : Finset ι) {f : ι -> α -> E} (hf : forall i in s, Int
egrable (f i) μ) : (se…
-/
theorem integral_finsetSum {ι} (s : Finset ι) {f : ι → α → G} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_finsetSum (dominatedFinMeasAdditive_weightedSMul _) s hf

@[deprecated (since := "2026-04-08")] alias integral_finset_sum := integral_finsetSum

@[integral_simps]
/-
**MeasureTheory.integral_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -∫ a, f a ∂μ
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_neg`：setToFun_neg (hT : DominatedFinMeasAdditive 
μ T C) (f : α -> E) : setToFun μ T hT (-f) = -setToFun μ T hT f
-/
theorem integral_neg (f : α → G) : ∫ a, -f a ∂μ = -∫ a, f a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_neg (dominatedFinMeasAdditive_weightedSMul μ) f
/-
**MeasureTheory.integral_neg'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_neg' (f : α -> G) : ∫ a, (-f) a ∂μ = -∫ a, f a ∂μ
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
-/
theorem integral_neg' (f : α → G) : ∫ a, (-f) a ∂μ = -∫ a, f a ∂μ :=
  integral_neg f
/-
**MeasureTheory.integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_sub {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) : 
∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_sub`：setToFun_sub (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f - g) = s
etToFun μ T hT f…
-/
theorem integral_sub {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_sub (dominatedFinMeasAdditive_weightedSMul μ) hf hg
/-
**MeasureTheory.integral_sub'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_sub' {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) :
 ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
-/
theorem integral_sub' {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
  integral_sub hf hg

/-- The Bochner integral is linear. Note this requires `𝕜` to be a normed division ring, in order
to ensure that for `c ≠ 0`, the function `c • f` is integrable iff `f` is. For an analogous
statement for more general rings with an *a priori* integrability assumption on `f`, see
`MeasureTheory.Integrable.integral_smul`. -/
@[integral_simps]
/-
**MeasureTheory.integral_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜 G] [SMulCommClass Real 𝕜 G] (c
 : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ
参数：c : 𝕜；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_smul`：setToFun_smul [NormedDivisionRing 𝕜] [Modul
e 𝕜 E] [NormSMulClass 𝕜 E] [Module 𝕜 F] [NormSMulClass 𝕜 F] (hT : DominatedFinMe
asAdditive μ T C)…
· 使用定理 `MeasureTheory.weightedSMul_smul`：weightedSMul_smul [SMul 𝕜 F] [SMulCommC
lass Real 𝕜 F] (c : 𝕜) (s : Set α) (x : F) : weightedSMul μ s (c • x) = c • weig
htedSMul μ s x

--- 原说明 ---
The Bochner integral is linear. Note this requires `𝕜` to be a normed division r
ing, in order
to ensure that for `c ≠ 0`, the function `c • f` is integrable iff `f` is. For a
n analogous
statement for more general rings with an *a priori* integrability assumption on 
`f`, see
`MeasureTheory.Integrable.integral_smul`.
-/
theorem integral_smul [Module 𝕜 G] [NormSMulClass 𝕜 G] [SMulCommClass ℝ 𝕜 G] (c : 𝕜) (f : α → G) :
    ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_smul (dominatedFinMeasAdditive_weightedSMul μ) weightedSMul_smul c f
/-
**MeasureTheory.Integrable.integral_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Integrable`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : No
rmedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {R : Type
 u_6} [inst_2 : NormedRing R] [inst_3 : _root_.Module R G] [IsBoundedSMul R G]  
 [SMulCommClass ℝ R G] (c : R) {f : α → G},   MeasureTheory.Integrable f μ → ∫ (
a : α), c • f a ∂μ = c • ∫ (a : α), f a ∂μ
参数：c : R；a : α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Integrable.fun_smul`：∀ {α : Type u_1} {β : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]  
 {𝕜 : Type u_8} [inst_1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `MeasureTheory.L1.integral_smul`：integral_smul (c : 𝕜) (f : α ->₁[μ] E) :
 integral (c • f) = c • integral f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Integrable.integral_smul {R : Type*} [NormedRing R] [Module R G] [IsBoundedSMul R G]
    [SMulCommClass ℝ R G] (c : R)
    {f : α → G} (hf : Integrable f μ) :
    ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simpa only [integral, hG, hf, hf.fun_smul c] using! L1.integral_smul c (toL1 f hf)
  · simp [integral, hG]
/-
**MeasureTheory.integral_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_const_mul {L : Type*} [RCLike L] (r : L) (f : α -> L) : ∫ a, r * 
f a ∂μ = r * ∫ a, f a ∂μ
参数：r : L；f : α -> L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem integral_const_mul {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ :=
  integral_smul r f
/-
**MeasureTheory.integral_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_mul_const {L : Type*} [RCLike L] (r : L) (f : α -> L) : ∫ a, f a 
* r ∂μ = (∫ a, f a ∂μ) * r
参数：r : L；f : α -> L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_mul_const {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r := by simp only [mul_comm, integral_const_mul r f]
/-
**MeasureTheory.integral_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_div {L : Type*} [RCLike L] (r : L) (f : α -> L) : ∫ a, f a / r ∂μ
 = (∫ a, f a ∂μ) / r
参数：r : L；f : α -> L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_mul_const`：integral_mul_const {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r
-/
theorem integral_div {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r := by
  simpa only [← div_eq_mul_inv] using integral_mul_const r⁻¹ f
/-
**MeasureTheory.integral_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_congr_ae {f g : α -> G} (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a 
∂μ
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
-/
theorem integral_congr_ae {f g : α → G} (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_congr_ae (dominatedFinMeasAdditive_weightedSMul μ) h
/-
**MeasureTheory.integral_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_congr_ae {f g : α -> G} (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a 
∂μ
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
-/
lemma integral_congr_ae₂ {β : Type*} {_ : MeasurableSpace β} {ν : Measure β} {f g : α → β → G}
    (h : ∀ᵐ a ∂μ, f a =ᵐ[ν] g a) :
    ∫ a, ∫ b, f a b ∂ν ∂μ = ∫ a, ∫ b, g a b ∂ν ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

@[simp]
/-
**MeasureTheory.L1.integral_of_fun_eq_integral'** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.L1`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : No
rmedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {f : α → 
G} (hf : MeasureTheory.Integrable f μ),   ∫ (a : α), ↑(MeasureTheory.AEEqFun.mk 
f ⋯) a ∂μ = ∫ (a : α), f a ∂μ
参数：hf : MeasureTheory.Integrable f μ；a : α；MeasureTheory.AEEqFun.mk f ⋯；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_toL1`：setToFun_toL1 (hT : DominatedFinMeasAdditiv
e μ T C) (hf : Integrable f μ) : setToFun μ T hT (hf.toL1 f) = setToFun μ T hT f
-/
theorem L1.integral_of_fun_eq_integral' {f : α → G} (hf : Integrable f μ) :
    ∫ a, (AEEqFun.mk f hf.aestronglyMeasurable) a ∂μ = ∫ a, f a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_toL1 (dominatedFinMeasAdditive_weightedSMul μ) hf
/-
**MeasureTheory.L1.integral_of_fun_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.L1`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : No
rmedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {f : α → 
G} (hf : MeasureTheory.Integrable f μ),   ∫ (a : α), ↑↑(MeasureTheory.Integrable
.toL1 f hf) a ∂μ = ∫ (a : α), f a ∂μ
参数：hf : MeasureTheory.Integrable f μ；a : α；MeasureTheory.Integrable.toL1 f hf；a 
: α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.integral_of_fun_eq_integral'`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem L1.integral_of_fun_eq_integral {f : α → G} (hf : Integrable f μ) :
    ∫ a, (hf.toL1 f) a ∂μ = ∫ a, f a ∂μ := by
  simp [hf]

@[continuity]
/-
**MeasureTheory.continuous_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：continuous_integral : Continuous fun f : α ->₁[μ] G => ∫ a, f a ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuous_setToFun`：continuous_setToFun (hT : DominatedFi
nMeasAdditive μ T C) : Continuous fun f : α ->₁[μ] E => setToFun μ T hT f
-/
theorem continuous_integral : Continuous fun f : α →₁[μ] G => ∫ a, f a ∂μ := by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun (dominatedFinMeasAdditive_weightedSMul μ)
/-
**MeasureTheory.norm_integral_le_lintegral_norm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：norm_integral_le_lintegral_norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ENNReal.to
Real (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ)
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.norm_setToFun_le_toReal`：norm_setToFun_le_toReal (hT : Dom
inatedFinMeasAdditive μ T C) (hC : 0 <= C) : ‖setToFun μ T hT f‖ <= NNReal.mk C 
hC * ENNReal.toReal (∫⁻ a, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_integral_le_lintegral_norm (f : α → G) :
    ‖∫ a, f a ∂μ‖ ≤ ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  simp only [integral_eq_setToFun]
  exact (norm_setToFun_le_toReal _ (by simp)).trans (by simp)
/-
**MeasureTheory.enorm_integral_le_lintegral_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：enorm_integral_le_lintegral_enorm (f : α -> G) : ‖∫ a, f a ∂μ‖ₑ <= ∫⁻ a, ‖
f a‖ₑ ∂μ
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.enorm_setToFun_le`：enorm_setToFun_le (hT : DominatedFinMea
sAdditive μ T C) (hC : 0 <= C) : ‖setToFun μ T hT f‖ₑ <= NNReal.mk C hC * ∫⁻ x, 
‖f x‖ₑ ∂μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem enorm_integral_le_lintegral_enorm (f : α → G) : ‖∫ a, f a ∂μ‖ₑ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := by
  simp only [integral_eq_setToFun]
  exact (enorm_setToFun_le _ (by simp)).trans (by simp)
/-
**MeasureTheory.dist_integral_le_lintegral_edist** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：dist_integral_le_lintegral_edist {f g : α -> G} (hf : Integrable f μ) (hg 
: Integrable g μ) : dist (∫ a, f a ∂μ) (∫ a, g a ∂μ) <= (∫⁻ a, edist (f a) (g a)
 ∂μ).toReal
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.norm_integral_le_lintegral_norm`：norm_integral_le_lintegra
l_norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a
‖ ∂μ)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
-/
theorem dist_integral_le_lintegral_edist
    {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (∫ a, f a ∂μ) (∫ a, g a ∂μ) ≤ (∫⁻ a, edist (f a) (g a) ∂μ).toReal := by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]
/-
**MeasureTheory.edist_integral_le_lintegral_edist** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：edist_integral_le_lintegral_edist {f g : α -> G} (hf : Integrable f μ) (hg
 : Integrable g μ) : edist (∫ a, f a ∂μ) (∫ a, g a ∂μ) <= ∫⁻ a, edist (f a) (g a
) ∂μ
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_le_of_le_toReal`：ofReal_le_of_le_toReal {a : Real} {b : R
eal>=0∞} (h : a <= ENNReal.toReal b) : ENNReal.ofReal a <= b
· 使用定理 `MeasureTheory.dist_integral_le_lintegral_edist`：dist_integral_le_lintegr
al_edist {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) : dist (∫ a,
 f a ∂μ) (∫ a, g a ∂μ) <= (∫⁻ a, edi…
-/
theorem edist_integral_le_lintegral_edist
    {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    edist (∫ a, f a ∂μ) (∫ a, g a ∂μ) ≤ ∫⁻ a, edist (f a) (g a) ∂μ := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_of_le_toReal (dist_integral_le_lintegral_edist hf hg)
/-
**MeasureTheory.integral_eq_zero_of_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integral_eq_zero_of_ae {f : α -> G} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0
参数：hf : f =ᵐ[μ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_zero_of_ae {f : α → G} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0 := by
  simp [integral_congr_ae hf, integral_zero]
/-
**MeasureTheory.frequently_ae_ne_zero_of_integral_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：frequently_ae_ne_zero_of_integral_ne_zero {f : α -> G} (h : ∫ a, f a ∂μ !=
 0) : existsᶠ a in ae μ, f a != 0
参数：h : ∫ a, f a ∂μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_eq_zero_of_ae`：integral_eq_zero_of_ae {f : α -> G
} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem frequently_ae_ne_zero_of_integral_ne_zero {f : α → G}
    (h : ∫ a, f a ∂μ ≠ 0) : ∃ᶠ a in ae μ, f a ≠ 0 :=
  fun h' ↦ h (integral_eq_zero_of_ae (h'.mono fun _ ↦ not_not.mp))
/-
**MeasureTheory.exists_ne_zero_of_integral_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：exists_ne_zero_of_integral_ne_zero {f : α -> G} (h : ∫ a, f a ∂μ != 0) : e
xists a, f a != 0
参数：h : ∫ a, f a ∂μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.frequently_ae_ne_zero_of_integral_ne_zero`：frequently_ae_n
e_zero_of_integral_ne_zero {f : α -> G} (h : ∫ a, f a ∂μ != 0) : existsᶠ a in ae
 μ, f a != 0
-/
theorem exists_ne_zero_of_integral_ne_zero {f : α → G}
    (h : ∫ a, f a ∂μ ≠ 0) : ∃ a, f a ≠ 0 :=
  (frequently_ae_ne_zero_of_integral_ne_zero h).exists

/-- If `f` has finite integral, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
/-
**MeasureTheory.HasFiniteIntegral.tendsto_setIntegral_nhds_zero** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : No
rmedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {ι : Type
 u_6} {f : α → G},   MeasureTheory.HasFiniteIntegral f μ →     ∀ {l : Filter ι} 
{s : ι → Set α},       Filter.Tendsto (⇑μ ∘ s) l (nhds 0) → Filter.Tendsto (fun 
i => ∫ (x : α) in s i, f x ∂μ) l (nhds 0)
参数：⇑μ ∘ s；nhds 0；fun i => ∫ (x : α) in s i, f x ∂μ；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `MeasureTheory.tendsto_setLIntegral_zero`：tendsto_setLIntegral_zero {ι} {
f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) {l : Filter ι} {s : ι -> Set α} (hl :
 Tendsto (μ ∘ s) l (𝓝 0)) : T…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.enorm_integral_le_lintegral_enorm`：enorm_integral_le_linte
gral_enorm (f : α -> G) : ‖∫ a, f a ∂μ‖ₑ <= ∫⁻ a, ‖f a‖ₑ ∂μ

--- 原说明 ---
If `f` has finite integral, then `∫ x in s, f x ∂μ` is absolutely continuous in 
`s`: it tends
to zero as `μ s` tends to zero.
-/
theorem HasFiniteIntegral.tendsto_setIntegral_nhds_zero {ι} {f : α → G}
    (hf : HasFiniteIntegral f μ) {l : Filter ι} {s : ι → Set α} (hs : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_setLIntegral_zero (ne_of_lt hf) hs) (fun i => zero_le)
    fun i => enorm_integral_le_lintegral_enorm _

/-- If `f` is integrable, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
/-
**MeasureTheory.Integrable.tendsto_setIntegral_nhds_zero** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : No
rmedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {ι : Type
 u_6} {f : α → G},   MeasureTheory.Integrable f μ →     ∀ {l : Filter ι} {s : ι 
→ Set α},       Filter.Tendsto (⇑μ ∘ s) l (nhds 0) → Filter.Tendsto (fun i => ∫ 
(x : α) in s i, f x ∂μ) l (nhds 0)
参数：⇑μ ∘ s；nhds 0；fun i => ∫ (x : α) in s i, f x ∂μ；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.tendsto_setIntegral_nhds_zero`：∀ {α : Ty
pe u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] 
{m : MeasurableSpace α}   {μ : MeasureTheory.Measur…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `f` is integrable, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: i
t tends
to zero as `μ s` tends to zero.
-/
theorem Integrable.tendsto_setIntegral_nhds_zero {ι} {f : α → G} (hf : Integrable f μ)
    {l : Filter ι} {s : ι → Set α} (hs : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) l (𝓝 0) :=
  hf.2.tendsto_setIntegral_nhds_zero hs

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x ∂μ`. -/
/-
**MeasureTheory.tendsto_integral_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：tendsto_integral_of_L1 {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) {
F : ι -> α -> G} {l : Filter ι} (hFi : forallᶠ i in l, Integrable (F i) μ) (hF :
 Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)) : Tendsto (fun i => ∫ x, F 
i x ∂μ) l (𝓝 <| ∫ x, f x ∂μ)
参数：f : α -> G；hfi : AEStronglyMeasurable f μ；hFi : forallᶠ i in l, Integrable (F
 i) μ；hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.tendsto_setToFun_of_L1`：tendsto_setToFun_of_L1 (hT : Domin
atedFinMeasAdditive μ T C) {ι} (f : α -> E) (hf : AEStronglyMeasurable f μ) {fs 
: ι -> α -> E} {l : Filter…

--- 原说明 ---
If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x ∂μ`.
-/
theorem tendsto_integral_of_L1 {ι} (f : α → G) (hfi : AEStronglyMeasurable f μ)
    {F : ι → α → G} {l : Filter ι} (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) := by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_of_L1 (dominatedFinMeasAdditive_weightedSMul μ) f hfi hFi hF

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x ∂μ`. -/
/-
**MeasureTheory.tendsto_integral_of_L1'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：tendsto_integral_of_L1' {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) 
{F : ι -> α -> G} {l : Filter ι} (hFi : forallᶠ i in l, Integrable (F i) μ) (hF 
: Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0)) : Tendsto (fun i => ∫ x, F i
 x ∂μ) l (𝓝 (∫ x, f x ∂μ))
参数：f : α -> G；hfi : AEStronglyMeasurable f μ；hFi : forallᶠ i in l, Integrable (F
 i) μ；hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_integral_of_L1`：tendsto_integral_of_L1 {ι} (f : α 
-> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G} {l : Filter ι} (hFi : f
orallᶠ i in l, Integrable …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ

--- 原说明 ---
If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x ∂μ`.
-/
lemma tendsto_integral_of_L1' {ι} (f : α → G) (hfi : AEStronglyMeasurable f μ)
    {F : ι → α → G} {l : Filter ι} (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

/-- If `F i → f` in `L1`, then `∫ x in s, F i x ∂μ → ∫ x in s, f x ∂μ`. -/
/-
**MeasureTheory.tendsto_setIntegral_of_L1** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_setIntegral_of_L1 {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ
) {F : ι -> α -> G} {l : Filter ι} (hFi : forallᶠ i in l, Integrable (F i) μ) (h
F : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)) (s : Set α) : Tendsto (f
un i => ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ))
参数：f : α -> G；hfi : AEStronglyMeasurable f μ；hFi : forallᶠ i in l, Integrable (F
 i) μ；hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_integral_of_L1`：tendsto_integral_of_L1 {ι} (f : α 
-> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G} {l : Filter ι} (hFi : f
orallᶠ i in l, Integrable …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.eLpNorm_mono_measure`：eLpNorm_mono_measure (f : α -> ε) (h
μν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ

--- 原说明 ---
If `F i → f` in `L1`, then `∫ x in s, F i x ∂μ → ∫ x in s, f x ∂μ`.
-/
lemma tendsto_setIntegral_of_L1 {ι} (f : α → G) (hfi : AEStronglyMeasurable f μ) {F : ι → α → G}
    {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0))
    (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi.restrict ?_ ?_
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ ↦ zero_le)
      (fun _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- If `F i → f` in `L1`, then `∫ x in s, F i x ∂μ → ∫ x in s, f x ∂μ`. -/
/-
**MeasureTheory.tendsto_setIntegral_of_L1'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：tendsto_setIntegral_of_L1' {ι} (f : α -> G) (hfi : AEStronglyMeasurable f 
μ) {F : ι -> α -> G} {l : Filter ι} (hFi : forallᶠ i in l, Integrable (F i) μ) (
hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0)) (s : Set α) : Tendsto (fu
n i => ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ))
参数：f : α -> G；hfi : AEStronglyMeasurable f μ；hFi : forallᶠ i in l, Integrable (F
 i) μ；hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0)；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendsto_setIntegral_of_L1`：tendsto_setIntegral_of_L1 {ι} (
f : α -> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G} {l : Filter ι} (h
Fi : forallᶠ i in l, Integrab…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ

--- 原说明 ---
If `F i → f` in `L1`, then `∫ x in s, F i x ∂μ → ∫ x in s, f x ∂μ`.
-/
lemma tendsto_setIntegral_of_L1' {ι} (f : α → G) (hfi : AEStronglyMeasurable f μ) {F : ι → α → G}
    {l : Filter ι} (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ) l (𝓝 0)) (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
/-
**MeasureTheory.continuousWithinAt_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：continuousWithinAt_of_dominated {F : X -> α -> G} {x₀ : X} {bound : α -> R
eal} {s : Set X} (hF_meas : forallᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ) 
(h_bound : forallᶠ x in 𝓝[s] x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a) (bound_integr
able : Integrable bound μ) (h_cont : forallᵐ a ∂μ, ContinuousWithinAt (fun x => 
F x a) s x₀) : ContinuousWithinAt (fun x => ∫ a, F x a ∂μ) s x₀
参数：hF_meas : forallᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ；h_bound : forall
ᶠ x in 𝓝[s] x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a；bound_integrable : Integrable b
ound μ；h_cont : forallᵐ a ∂μ, ContinuousWithinAt (fun x => F x a) s x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuousWithinAt_setToFun_of_dominated`：continuousWithin
At_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E
} {x₀ : X} {bound : α -> Real} {s : Set X} (…
-/
theorem continuousWithinAt_of_dominated {F : X → α → G} {x₀ : X} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousWithinAt (fun x => F x a) s x₀) :
    ContinuousWithinAt (fun x => ∫ a, F x a ∂μ) s x₀ := by
  simp only [integral_eq_setToFun]
  exact continuousWithinAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont
/-
**MeasureTheory.continuousAt_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：continuousAt_of_dominated {F : X -> α -> G} {x₀ : X} {bound : α -> Real} (
hF_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (h_bound : forallᶠ x 
in 𝓝 x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a) (bound_integrable : Integrable bound 
μ) (h_cont : forallᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀) : ContinuousAt (fun
 x => ∫ a, F x a ∂μ) x₀
参数：hF_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ；h_bound : forallᶠ x
 in 𝓝 x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a；bound_integrable : Integrable bound μ
；h_cont : forallᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuousAt_setToFun_of_dominated`：continuousAt_setToFun_
of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E} {x₀ : X} {
bound : α -> Real} (hfs_meas : forallᶠ…
-/
theorem continuousAt_of_dominated {F : X → α → G} {x₀ : X} {bound : α → ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x => ∫ a, F x a ∂μ) x₀ := by
  simp only [integral_eq_setToFun]
  exact continuousAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont
/-
**MeasureTheory.continuousOn_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：continuousOn_of_dominated {F : X -> α -> G} {bound : α -> Real} {s : Set X
} (hF_meas : forall x in s, AEStronglyMeasurable (F x) μ) (h_bound : forall x in
 s, forallᵐ a ∂μ, ‖F x a‖ <= bound a) (bound_integrable : Integrable bound μ) (h
_cont : forallᵐ a ∂μ, ContinuousOn (fun x => F x a) s) : ContinuousOn (fun x => 
∫ a, F x a ∂μ) s
参数：hF_meas : forall x in s, AEStronglyMeasurable (F x) μ；h_bound : forall x in s
, forallᵐ a ∂μ, ‖F x a‖ <= bound a；bound_integrable : Integrable bound μ；h_cont 
: forallᵐ a ∂μ, ContinuousOn (fun x => F x a) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuousOn_setToFun_of_dominated`：continuousOn_setToFun_
of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E} {bound : α
 -> Real} {s : Set X} (hfs_meas : fora…
-/
theorem continuousOn_of_dominated {F : X → α → G} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousOn (fun x => F x a) s) :
    ContinuousOn (fun x => ∫ a, F x a ∂μ) s := by
  simp only [integral_eq_setToFun]
  exact continuousOn_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont
/-
**MeasureTheory.continuous_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：continuous_of_dominated {F : X -> α -> G} {bound : α -> Real} (hF_meas : f
orall x, AEStronglyMeasurable (F x) μ) (h_bound : forall x, forallᵐ a ∂μ, ‖F x a
‖ <= bound a) (bound_integrable : Integrable bound μ) (h_cont : forallᵐ a ∂μ, Co
ntinuous fun x => F x a) : Continuous fun x => ∫ a, F x a ∂μ
参数：hF_meas : forall x, AEStronglyMeasurable (F x) μ；h_bound : forall x, forallᵐ 
a ∂μ, ‖F x a‖ <= bound a；bound_integrable : Integrable bound μ；h_cont : forallᵐ 
a ∂μ, Continuous fun x => F x a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuous_setToFun_of_dominated`：continuous_setToFun_of_d
ominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E} {bound : α -> 
Real} (hfs_meas : forall x, AEStrong…
-/
theorem continuous_of_dominated {F : X → α → G} {bound : α → ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) μ) (h_bound : ∀ x, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ) (h_cont : ∀ᵐ a ∂μ, Continuous fun x => F x a) :
    Continuous fun x => ∫ a, F x a ∂μ := by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

/-- The Bochner integral of a real-valued function `f : α → ℝ` is the difference between the
  integral of the positive part of `f` and the integral of the negative part of `f`. -/
/-
**MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_eq_lintegral_pos_part_sub_lintegral_neg_part {f : α -> Real} (hf 
: Integrable f μ) : ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, .ofReal (f a) ∂μ) - ENNR
eal.toReal (∫⁻ a, .ofReal (-f a) ∂μ)
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.norm_def`：norm_def (f : α ->₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a
‖ₑ ∂μ).toReal
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.coeFn_toL1`：coeFn_toL1 {f : α -> β} (hf : Integ
rable f μ) : hf.toL1 f =ᵐ[μ] f
· 使用定理 `MeasureTheory.Lp.coeFn_posPart`：coeFn_posPart (f : Lp Real p μ) : ⇑(posP
art f) =ᵐ[μ] fun a => max (f a) 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Real.nnnorm_of_nonneg`：nnnorm_of_nonneg (hr : 0 <= r) : ‖r‖₊ = .mk r hr
· 使用定理 `Real.coe_toNNReal'`：coe_toNNReal' (r : Real) : (Real.toNNReal r : Real) 
= max r 0
· 使用定理 `NNReal.coe_mk`：∀ (a : ℝ) (ha : 0 ≤ a), ↑(NNReal.mk a ha) = a
· 使用定理 `MeasureTheory.Lp.coeFn_negPart`：coeFn_negPart (f : Lp Real p μ) : forall
ᵐ a ∂μ, negPart f a = -min (f a) 0
· 使用定理 `nnnorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖
₊ = ‖a‖₊
· 使用定理 `Real.norm_of_nonpos`：norm_of_nonpos (hr : r <= 0) : ‖r‖ = -r
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_neg_neg`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOr
der α] [IsOrderedAddMonoid α] (a b : α),   max (-a) (-b) = -min a b
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MeasureTheory.L1.integral_eq_norm_posPart_sub`：integral_eq_norm_posPart_
sub (f : α ->₁[μ] Real) : integral f = ‖Lp.posPart f‖ - ‖Lp.negPart f‖

--- 原说明 ---
The Bochner integral of a real-valued function `f : α → ℝ` is the difference bet
ween the
  integral of the positive part of `f` and the integral of the negative part of 
`f`.
-/
theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part {f : α → ℝ} (hf : Integrable f μ) :
    ∫ a, f a ∂μ =
      ENNReal.toReal (∫⁻ a, .ofReal (f a) ∂μ) - ENNReal.toReal (∫⁻ a, .ofReal (-f a) ∂μ) := by
  let f₁ := hf.toL1 f
  -- Go to the `L¹` space
  have eq₁ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) = ‖Lp.posPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_posPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁, h₂, ENNReal.ofReal]
    congr 1
    apply NNReal.eq
    rw [Real.nnnorm_of_nonneg (le_max_right _ _)]
    rw [Real.coe_toNNReal', NNReal.coe_mk]
  -- Go to the `L¹` space
  have eq₂ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (-f a) ∂μ) = ‖Lp.negPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_negPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁, h₂, ENNReal.ofReal]
    congr 1
    apply NNReal.eq
    simp only [Real.coe_toNNReal', coe_nnnorm, nnnorm_neg]
    rw [Real.norm_of_nonpos (min_le_right _ _), ← max_neg_neg, neg_zero]
  rw [eq₁, eq₂, integral, dif_pos, dif_pos]
  exact L1.integral_eq_norm_posPart_sub _
/-
**MeasureTheory.integral_eq_lintegral_of_nonneg_ae** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：integral_eq_lintegral_of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm 
: AEStronglyMeasurable f μ) : ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal
 (f a) ∂μ)
参数：hf : 0 <=ᵐ[μ] f；hfm : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part`：int
egral_eq_lintegral_pos_part_sub_lintegral_neg_part {f : α -> Real} (hf : Integra
ble f μ) : ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, .ofReal (f…
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `ENNReal.measurable_ofReal`：measurable_ofReal : Measurable ENNReal.ofReal
· 使用定理 `AEMeasurable.neg`：∀ {G : Type u_2} {α : Type u_3} [inst : Neg G] [inst_1
 : MeasurableSpace G] [MeasurableNeg G] {m : MeasurableSpace α}   {f : α → G} {μ
 : Mea…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_top`：⊤.toReal = 0
-/
theorem integral_eq_lintegral_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f)
    (hfm : AEStronglyMeasurable f μ) :
    ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) := by
  by_cases hfi : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
    have h_min : ∫⁻ a, ENNReal.ofReal (-f a) ∂μ = 0 := by
      rw [lintegral_eq_zero_iff']
      · refine hf.mono ?_
        simp only [Pi.zero_apply]
        intro a h
        simp only [h, neg_nonpos, ofReal_eq_zero]
      · exact measurable_ofReal.comp_aemeasurable hfm.aemeasurable.neg
    rw [h_min, toReal_zero, _root_.sub_zero]
  · rw [integral_undef hfi]
    simp_rw [Integrable, hfm, hasFiniteIntegral_iff_norm, lt_top_iff_ne_top, Ne, true_and,
      Classical.not_not] at hfi
    have : ∫⁻ a : α, ENNReal.ofReal (f a) ∂μ = ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ := by
      refine lintegral_congr_ae (hf.mono fun a h => ?_)
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg h]
    rw [this, hfi, toReal_top]
/-
**MeasureTheory.integral_norm_eq_lintegral_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α
 -> P} (hf : AEStronglyMeasurable f μ) : ∫ x, ‖f x‖ ∂μ = (∫⁻ x, ‖f x‖ₑ ∂μ).toRea
l
参数：hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α → P}
    (hf : AEStronglyMeasurable f μ) : ∫ x, ‖f x‖ ∂μ = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hf.norm]
  · simp_rw [ofReal_norm]
  · filter_upwards; simp_rw [Pi.zero_apply, norm_nonneg, imp_true_iff]
/-
**MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：ofReal_integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P]
 {f : α -> P} (hf : Integrable f μ) : ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) = ∫⁻ x, ‖f 
x‖ₑ ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_norm_eq_lintegral_enorm`：integral_norm_eq_lintegr
al_enorm {P : Type*} [NormedAddCommGroup P] {f : α -> P} (hf : AEStronglyMeasura
ble f μ) : ∫ x, ‖f x‖ ∂μ = (∫⁻ x, ‖f…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_enorm`：hasFiniteIntegral_iff_enorm {
f : α -> ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ofReal_integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α → P}
    (hf : Integrable f μ) : ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable, ENNReal.ofReal_toReal]
  exact lt_top_iff_ne_top.mp (hasFiniteIntegral_iff_enorm.mpr hf.2)
/-
**MeasureTheory.SimpleFunc.integral_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} [Complete
Space E] (f : MeasureTheory.SimpleFunc α E),   MeasureTheory.Integrable (⇑f) μ →
 MeasureTheory.SimpleFunc.integral μ f = ∫ (x : α), f x ∂μ
参数：f : MeasureTheory.SimpleFunc α E；⇑f；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq`：integral_eq [hE : CompleteSpace E] (f : α -> 
E) (hf : Integrable f μ) : ∫ a, f a ∂μ = L1.integral (hf.toL1 f)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.L1.SimpleFunc.toLp_one_eq_toL1`：∀ {α : Type u_1} {E : Type
 u_4} [inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureThe
ory.Measure α}   (f : MeasureTheor…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral_L1_eq_integral`：∀ {α : Type u_1} {E
 : Type u_2} [inst : NormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureT
heory.Measure α}   [inst_1 : NormedSpace …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integral_eq_integral`：integral_eq_integral (
f : α ->₁ₛ[μ] E) : integral f = (toSimpleFunc f).integral μ
· 使用定理 `MeasureTheory.SimpleFunc.integral_congr`：integral_congr {f g : α ->ₛ E} 
(hf : Integrable f μ) (h : f =ᵐ[μ] g) : f.integral μ = g.integral μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_toLp`：toSimpleFunc_toLp (f : α 
->ₛ E) (hfi : MemLp f p μ) : toSimpleFunc (toLp f hfi) =ᵐ[μ] f
-/
theorem SimpleFunc.integral_eq_integral [CompleteSpace E] (f : α →ₛ E) (hfi : Integrable f μ) :
    f.integral μ = ∫ x, f x ∂μ := by
  rw [MeasureTheory.integral_eq f hfi, ← L1.SimpleFunc.toLp_one_eq_toL1,
    L1.SimpleFunc.integral_L1_eq_integral, L1.SimpleFunc.integral_eq_integral]
  exact SimpleFunc.integral_congr hfi (Lp.simpleFunc.toSimpleFunc_toLp _ _).symm
/-
**MeasureTheory.SimpleFunc.integral_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} [Complete
Space E] (f : MeasureTheory.SimpleFunc α E),   MeasureTheory.Integrable (⇑f) μ →
 ∫ (x : α), f x ∂μ = ∑ x ∈ f.range, μ.real (⇑f ⁻¹' {x}) • x
参数：f : MeasureTheory.SimpleFunc α E；⇑f；x : α；⇑f ⁻¹' {x}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq_integral`：∀ {α : Type u_1} {E : Typ
e u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.SimpleFunc.integral.eq_1`：∀ {α : Type u_1} {F : Type u_3} 
[inst : NormedAddCommGroup F] [inst_1 : NormedSpace ℝ F] {x : MeasurableSpace α}
   (μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq`：integral_eq {m : MeasurableSpace α
} (μ : Measure α) (f : α ->ₛ F) : f.integral μ = ∑ x in f.range, μ.real (f ⁻¹' {
x}) • x
-/
theorem SimpleFunc.integral_eq_sum [CompleteSpace E] (f : α →ₛ E) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) • x := by
  rw [← f.integral_eq_integral hfi, SimpleFunc.integral, ← SimpleFunc.integral_eq]; rfl
/-
**MeasureTheory.tendsto_integral_approxOn_of_measurable** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendsto_integral_approxOn_of_measurable [CompleteSpace E] [MeasurableSpace
 E] [BorelSpace E] {f : α -> E} {s : Set E} [SeparableSpace s] (hfi : Integrable
 f μ) (hfm : Measurable f) (hs : forallᵐ x ∂μ, f x in closure s) {y₀ : E} (h₀ : 
y₀ in s) (h₀i : Integrable (fun _ => y₀) μ) : Tendsto (fun n => (SimpleFunc.appr
oxOn f hfm s y₀ h₀ n).integral μ) atTop (𝓝 <| ∫ x, f x ∂μ)
参数：hfi : Integrable f μ；hfm : Measurable f；hs : forallᵐ x ∂μ, f x in closure s；h
₀ : y₀ in s；h₀i : Integrable (fun _ => y₀) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.SimpleFunc.integrable_approxOn`：integrable_approxOn [Borel
Space E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) (hf : Integrable f 
μ) {s : Set E} {y₀ : E} (h₀ : y₀ i…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq_integral`：∀ {α : Type u_1} {E : Typ
e u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.integral_def`：∀ {α : Type u_5} {E : Type u_6} [inst : N
ormedAddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [in
st_1 : NormedSpace …
· 使用定理 `MeasureTheory.tendsto_setToFun_approxOn_of_measurable`：tendsto_setToFun_
approxOn_of_measurable (hT : DominatedFinMeasAdditive μ T C) [MeasurableSpace E]
 [BorelSpace E] {f : α -> E} {s : Set E} [S…
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
-/
theorem tendsto_integral_approxOn_of_measurable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : α → E} {s : Set E} [SeparableSpace s] (hfi : Integrable f μ) (hfm : Measurable f)
    (hs : ∀ᵐ x ∂μ, f x ∈ closure s) {y₀ : E} (h₀ : y₀ ∈ s) (h₀i : Integrable (fun _ => y₀) μ) :
    Tendsto (fun n => (SimpleFunc.approxOn f hfm s y₀ h₀ n).integral μ)
      atTop (𝓝 <| ∫ x, f x ∂μ) := by
  have hfi' := SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i
  simp only [SimpleFunc.integral_eq_integral _ (hfi' _), integral, L1.integral]
  exact tendsto_setToFun_approxOn_of_measurable (dominatedFinMeasAdditive_weightedSMul μ)
    hfi hfm hs h₀ h₀i
/-
**MeasureTheory.tendsto_integral_approxOn_of_measurable_of_range_subset** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_integral_approxOn_of_measurable_of_range_subset [CompleteSpace E] 
[MeasurableSpace E] [BorelSpace E] {f : α -> E} (fmeas : Measurable f) (hf : Int
egrable f μ) (s : Set E) [SeparableSpace s] (hs : range f union {0} subseteq s) 
: Tendsto (fun n => (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n).integral
 μ) atTop (𝓝 <| ∫ x, f x ∂μ)
参数：fmeas : Measurable f；hf : Integrable f μ；s : Set E；hs : range f union {0} sub
seteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_integral_approxOn_of_measurable`：tendsto_integral_
approxOn_of_measurable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {f :
 α -> E} {s : Set E} [SeparableSpace s] (hf…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
-/
theorem tendsto_integral_approxOn_of_measurable_of_range_subset
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : α → E} (fmeas : Measurable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s]
    (hs : range f ∪ {0} ⊆ s) :
    Tendsto (fun n => (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n).integral μ) atTop
      (𝓝 <| ∫ x, f x ∂μ) := by
  apply tendsto_integral_approxOn_of_measurable hf fmeas _ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

-- We redeclare `E` here to temporarily avoid
-- the `[NormedSpace ℝ E]` instance.
/-
**MeasureTheory.tendsto_integral_norm_approxOn_sub** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：tendsto_integral_norm_approxOn_sub {E : Type*} [NormedAddCommGroup E] [Mea
surableSpace E] [BorelSpace E] {f : α -> E} (fmeas : Measurable f) (hf : Integra
ble f μ) [SeparableSpace (range f union {0} : Set E)] : Tendsto (fun n => ∫ x, ‖
SimpleFunc.approxOn f fmeas (range f union {0}) 0 (by simp) n x - f x‖ ∂μ) atTop
 (𝓝 0)
参数：fmeas : Measurable f；hf : Integrable f μ；range f union {0} : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_norm_eq_lintegral_enorm`：integral_norm_eq_lintegr
al_enorm {P : Type*} [NormedAddCommGroup P] {f : α -> P} (hf : AEStronglyMeasura
ble f μ) : ∫ x, ‖f x‖ ∂μ = (∫⁻ x, ‖f…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.aestronglyMeasurable`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   (f : MeasureTheory.Simp…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `stronglyMeasurable_iff_measurable_separable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.IsSeparable.mono`：∀ {α : Type u} [t : TopologicalSpace 
α] {s u : Set α},   TopologicalSpace.IsSeparable s → u ⊆ s → TopologicalSpace.Is
Separable u
· 使用定理 `TopologicalSpace.IsSeparable.of_subtype`：∀ {α : Type u} [t : Topological
Space α] (s : Set α) [TopologicalSpace.SeparableSpace ↑s], TopologicalSpace.IsSe
parable s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.approxOn.congr_simp`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : PseudoEMetricSpace α]   [inst_2 : Ope
nsMeasurableSpace α] [inst_3 : Mea…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toReal`：tendsto_toReal {a : Real>=0∞} (ha : a != ∞) : Te
ndsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal)
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn_range_L1_enorm`：tendsto_approx
On_range_L1_enorm [OpensMeasurableSpace E] {f : β -> E} {μ : Measure β} [Separab
leSpace (range f union {0} : Set E)] (fmeas : …
-/
theorem tendsto_integral_norm_approxOn_sub
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {f : α → E}
    (fmeas : Measurable f) (hf : Integrable f μ) [SeparableSpace (range f ∪ {0} : Set E)] :
    Tendsto (fun n ↦ ∫ x, ‖SimpleFunc.approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖ ∂μ)
      atTop (𝓝 0) := by
  convert! (tendsto_toReal zero_ne_top).comp (tendsto_approxOn_range_L1_enorm fmeas hf) with n
  rw [integral_norm_eq_lintegral_enorm]
  · simp
  · apply (SimpleFunc.aestronglyMeasurable _).sub
    apply (stronglyMeasurable_iff_measurable_separable.2 ⟨fmeas, ?_⟩).aestronglyMeasurable
    exact .mono (.of_subtype (range f ∪ {0})) subset_union_left
/-
**MeasureTheory.integral_eq_integral_pos_part_sub_integral_neg_part** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_eq_integral_pos_part_sub_integral_neg_part {f : α -> Real} (hf : 
Integrable f μ) : ∫ a, f a ∂μ = ∫ a, (Real.toNNReal (f a) : Real) ∂μ - ∫ a, (Rea
l.toNNReal (-f a) : Real) ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.real_toNNReal`：∀ {α : Type u_1} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrable f
 μ → MeasureTheory.Integrabl…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `max_zero_sub_max_neg_zero_eq_self`：∀ {α : Type u_1} [inst : AddGroup α] 
[inst_1 : LinearOrder α] [AddLeftMono α] (a : α), max a 0 - max (-a) 0 = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_integral_pos_part_sub_integral_neg_part {f : α → ℝ} (hf : Integrable f μ) :
    ∫ a, f a ∂μ = ∫ a, (Real.toNNReal (f a) : ℝ) ∂μ - ∫ a, (Real.toNNReal (-f a) : ℝ) ∂μ := by
  rw [← integral_sub hf.real_toNNReal]
  · simp
  · exact hf.neg.real_toNNReal
/-
**MeasureTheory.integral_abs_eq_two_mul_integral_posPart_sub_integral** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_abs_eq_two_mul_integral_posPart_sub_integral {f : α -> Real} (hf 
: Integrable f μ) : ∫ x, |f x| ∂μ = 2 * ∫ x, (f x)⁺ ∂μ - ∫ x, f x ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.pos_part`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrable f μ → 
MeasureTheory.Integrabl…
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
-/
theorem integral_abs_eq_two_mul_integral_posPart_sub_integral {f : α → ℝ} (hf : Integrable f μ) :
    ∫ x, |f x| ∂μ = 2 * ∫ x, (f x)⁺ ∂μ - ∫ x, f x ∂μ := by
  simp only [PosPart.posPart]
  have h_eq : ∀ x, |f x| = 2 * max (f x) 0 - f x := by grind
  rw [integral_congr_ae (Eventually.of_forall h_eq), integral_sub (by fun_prop) hf,
    integral_const_mul]
/-
**MeasureTheory.integral_abs_eq_two_mul_integral_negPart_add_integral** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_abs_eq_two_mul_integral_negPart_add_integral {f : α -> Real} (hf 
: Integrable f μ) : ∫ x, |f x| ∂μ = 2 * ∫ x, (f x)⁻ ∂μ + ∫ x, f x ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.neg_part`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrable f μ → 
MeasureTheory.Integrabl…
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
-/
theorem integral_abs_eq_two_mul_integral_negPart_add_integral {f : α → ℝ} (hf : Integrable f μ) :
    ∫ x, |f x| ∂μ = 2 * ∫ x, (f x)⁻ ∂μ + ∫ x, f x ∂μ := by
  simp only [NegPart.negPart]
  have h_eq : ∀ x, |f x| = 2 * max (-f x) 0 + f x := by grind
  rw [integral_congr_ae (Eventually.of_forall h_eq), integral_add (by fun_prop) hf,
    integral_const_mul]

end Basic

section Order

variable [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

@[gcongr]
/-
**MeasureTheory.integral_mono_measure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_mono_measure [OrderClosedTopology E] {f : α -> E} {ν : Measure α}
 (hle : μ <= ν) (hf : 0 <=ᵐ[ν] f) (hfi : Integrable f ν) : ∫ (a : α), f a ∂μ <= 
∫ (a : α), f a ∂ν
参数：hle : μ <= ν；hf : 0 <=ᵐ[ν] f；hfi : Integrable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.exists_stronglyMeasurable_range_subse
t`：exists_stronglyMeasurable_range_subset {α β : Type*} [TopologicalSpace β] [Ps
eudoMetrizableSpace β] [mb : MeasurableSpace β] [BorelSpace β] …
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Set.nonempty_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set.Ici
 a).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.tendsto_integral_approxOn_of_measurable_of_range_subset`：t
endsto_integral_approxOn_of_measurable_of_range_subset [CompleteSpace E] [Measur
ableSpace E] [BorelSpace E] {f : α -> E} (fmeas : Measurabl…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `MeasureTheory.SimpleFunc.integral_mono_measure`：integral_mono_measure {ν
} {f : α ->ₛ F} (hf : 0 <=ᵐ[ν] f) (hμν : μ <= ν) (hfν : Integrable f ν) : f.inte
gral μ <= f.integral ν
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `MeasureTheory.SimpleFunc.approxOn_range_nonneg`：approxOn_range_nonneg [Z
ero α] [Preorder α] {f : β -> α} (hf : 0 <= f) {hfm : Measurable f} [SeparableSp
ace (range f union {0} : Set α)] (n …
· 使用定理 `MeasureTheory.SimpleFunc.integrable_approxOn_range`：integrable_approxOn_
range [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) [Separa
bleSpace (range f union {0} : Set E)] (h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 33 条，此处仅展示前 30 条）
-/
lemma integral_mono_measure [OrderClosedTopology E] {f : α → E} {ν : Measure α} (hle : μ ≤ ν)
    (hf : 0 ≤ᵐ[ν] f) (hfi : Integrable f ν) : ∫ (a : α), f a ∂μ ≤ ∫ (a : α), f a ∂ν := by
  by_cases hE : CompleteSpace E
  swap; · simp [integral, hE]
  borelize E
  obtain ⟨g, hg, hg_nonneg, hfg⟩ := hfi.1.exists_stronglyMeasurable_range_subset
    isClosed_Ici.measurableSet (Set.nonempty_Ici (a := 0)) hf
  rw [integrable_congr hfg] at hfi
  simp only [integral_congr_ae hfg, integral_congr_ae (ae_mono hle hfg)]
  have _ := hg.separableSpace_range_union_singleton (b := 0)
  have h₁ := tendsto_integral_approxOn_of_measurable_of_range_subset hg.measurable hfi _ le_rfl
  have h₂ := tendsto_integral_approxOn_of_measurable_of_range_subset hg.measurable
    (hfi.mono_measure hle) _ le_rfl
  apply le_of_tendsto_of_tendsto' h₂ h₁
  exact fun n ↦ SimpleFunc.integral_mono_measure
    (Eventually.of_forall <| SimpleFunc.approxOn_range_nonneg hg_nonneg n) hle
    (SimpleFunc.integrable_approxOn_range _ hfi n)

variable [ClosedIciTopology E]

/-- The integral of a function which is nonnegative almost everywhere is nonnegative. -/
/-
**MeasureTheory.integral_nonneg_of_ae** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_nonneg_of_ae {f : α -> E} (hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
参数：hf : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `MeasureTheory.setToFun_nonneg`：setToFun_nonneg [ClosedIciTopology G''] {
T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C) 
(hT_nonneg : forall…
· 使用定理 `MeasureTheory.weightedSMul_nonneg`：weightedSMul_nonneg [PartialOrder F] 
[IsOrderedModule Real F] (s : Set α) (x : F) (hx : 0 <= x) : 0 <= weightedSMul μ
 s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f

--- 原说明 ---
The integral of a function which is nonnegative almost everywhere is nonnegative
.
-/
lemma integral_nonneg_of_ae {f : α → E} (hf : 0 ≤ᵐ[μ] f) :
    0 ≤ ∫ x, f x ∂μ :=
  integral_eq_setToFun f ▸ setToFun_nonneg (dominatedFinMeasAdditive_weightedSMul μ)
    (fun s _ _ => weightedSMul_nonneg s) hf
/-
**MeasureTheory.integral_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_nonneg {f : α -> E} (hf : 0 <= f) : 0 <= ∫ x, f x ∂μ
参数：hf : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma integral_nonneg {f : α → E} (hf : 0 ≤ f) :
    0 ≤ ∫ x, f x ∂μ :=
  integral_nonneg_of_ae (ae_of_all _ hf)
/-
**MeasureTheory.integral_nonpos_of_ae** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_nonpos_of_ae {f : α -> E} (hf : f <=ᵐ[μ] 0) : ∫ x, f x ∂μ <= 0
参数：hf : f <=ᵐ[μ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma integral_nonpos_of_ae {f : α → E} (hf : f ≤ᵐ[μ] 0) :
    ∫ x, f x ∂μ ≤ 0 := by
  rw [← neg_nonneg, ← integral_neg]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf] with x hx
  simpa
/-
**MeasureTheory.integral_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_nonpos {f : α -> E} (hf : f <= 0) : ∫ x, f x ∂μ <= 0
参数：hf : f <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_nonpos_of_ae`：integral_nonpos_of_ae {f : α -> E} 
(hf : f <=ᵐ[μ] 0) : ∫ x, f x ∂μ <= 0
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma integral_nonpos {f : α → E} (hf : f ≤ 0) :
    ∫ x, f x ∂μ ≤ 0 :=
  integral_nonpos_of_ae (ae_of_all _ hf)
/-
**MeasureTheory.integral_mono_ae** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_mono_ae {f g : α -> E} (hf : Integrable f μ) (hg : Integrable g μ
) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
参数：hf : Integrable f μ；hg : Integrable g μ；h : f <=ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma integral_mono_ae {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f ≤ᵐ[μ] g) : ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
  rw [← sub_nonneg, ← integral_sub hg hf]
  refine integral_nonneg_of_ae ?_
  filter_upwards [h] with x hx
  simpa

@[gcongr, mono]
/-
**MeasureTheory.integral_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_mono {f g : α -> E} (hf : Integrable f μ) (hg : Integrable g μ) (
h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
参数：hf : Integrable f μ；hg : Integrable g μ；h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma integral_mono {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f ≤ g) : ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ :=
  integral_mono_ae hf hg (ae_of_all _ h)
/-
**MeasureTheory.integral_mono_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：integral_mono_of_nonneg {f g : α -> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable
 g μ) (h : f <=ᵐ[μ] g) : ∫ a, f a ∂μ <= ∫ a, g a ∂μ
参数：hf : 0 <=ᵐ[μ] f；hgi : Integrable g μ；h : f <=ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
-/
lemma integral_mono_of_nonneg {f g : α → E} (hf : 0 ≤ᵐ[μ] f) (hgi : Integrable g μ)
    (h : f ≤ᵐ[μ] g) : ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ := by
  by_cases hfi : Integrable f μ
  · exact integral_mono_ae hfi hgi h
  · exact integral_undef hfi ▸ integral_nonneg_of_ae (hf.trans h)
/-
**MeasureTheory.integral_monotoneOn_of_integrand_ae** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：integral_monotoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : α -> β -
> E} {s : Set β} (hf_mono : forallᵐ x ∂μ, MonotoneOn (f x) s) (hf_int : forall a
 in s, Integrable (f · a) μ) : MonotoneOn (fun b => ∫ x, f x b ∂μ) s
参数：hf_mono : forallᵐ x ∂μ, MonotoneOn (f x) s；hf_int : forall a in s, Integrable
 (f · a) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma integral_monotoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : α → β → E}
    {s : Set β} (hf_mono : ∀ᵐ x ∂μ, MonotoneOn (f x) s)
    (hf_int : ∀ a ∈ s, Integrable (f · a) μ) : MonotoneOn (fun b => ∫ x, f x b ∂μ) s := by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int a ha) (hf_int b hb) ?_
  filter_upwards [hf_mono] with x hx
  exact hx ha hb hab
/-
**MeasureTheory.integral_antitoneOn_of_integrand_ae** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：integral_antitoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : α -> β -
> E} {s : Set β} (hf_anti : forallᵐ x ∂μ, AntitoneOn (f x) s) (hf_int : forall a
 in s, Integrable (f · a) μ) : AntitoneOn (fun b => ∫ x, f x b ∂μ) s
参数：hf_anti : forallᵐ x ∂μ, AntitoneOn (f x) s；hf_int : forall a in s, Integrable
 (f · a) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma integral_antitoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : α → β → E}
    {s : Set β} (hf_anti : ∀ᵐ x ∂μ, AntitoneOn (f x) s)
    (hf_int : ∀ a ∈ s, Integrable (f · a) μ) : AntitoneOn (fun b => ∫ x, f x b ∂μ) s := by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int b hb) (hf_int a ha) ?_
  filter_upwards [hf_anti] with x hx
  exact hx ha hb hab
/-
**MeasureTheory.integral_convexOn_of_integrand_ae** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integral_convexOn_of_integrand_ae {β : Type*} [AddCommMonoid β] [Module Re
al β] {f : α -> β -> E} {s : Set β} (hs : Convex Real s) (hf_conv : forallᵐ x ∂μ
, ConvexOn Real s (f x)) (hf_int : forall a in s, Integrable (f · a) μ) : Convex
On Real s (fun b => ∫ x, f x b ∂μ)
参数：hs : Convex Real s；hf_conv : forallᵐ x ∂μ, ConvexOn Real s (f x)；hf_int : for
all a in s, Integrable (f · a) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convex_iff_add_mem`：convex_iff_add_mem : Convex 𝕜 s ↔ forall ⦃x⦄, x in s
 -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> a •
 x + b •…
· 使用定理 `MeasureTheory.Integrable.fun_add`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   
[inst_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.fun_smul_enorm`：∀ {α : Type u_1} {m : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} {ε : Type u_9}   [inst : 
TopologicalSpace ε] [inst_1 :…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_convexOn_of_integrand_ae {β : Type*} [AddCommMonoid β]
    [Module ℝ β] {f : α → β → E} {s : Set β} (hs : Convex ℝ s)
    (hf_conv : ∀ᵐ x ∂μ, ConvexOn ℝ s (f x)) (hf_int : ∀ a ∈ s, Integrable (f · a) μ) :
    ConvexOn ℝ s (fun b => ∫ x, f x b ∂μ) := by
  refine ⟨hs, ?_⟩
  intro a ha b hb p q hp hq hpq
  calc ∫ x, f x (p • a + q • b) ∂μ ≤ ∫ x, p • f x a + q • f x b ∂μ := by
                  refine integral_mono_ae ?lhs ?rhs ?ae_le
                  case lhs =>
                    refine hf_int _ ?_
                    rw [convex_iff_add_mem] at hs
                    exact hs ha hb hp hq hpq
                  case rhs => fun_prop (disch := aesop)
                  case ae_le =>
                    filter_upwards [hf_conv] with x hx
                    exact hx.2 ha hb hp hq hpq
            _ = ∫ x, p • f x a ∂μ + ∫ x, q • f x b ∂μ := by
                  apply integral_add
                  all_goals fun_prop (disch := aesop)
            _ = p • ∫ x, f x a ∂μ + q • ∫ x, f x b ∂μ := by simp [integral_smul]
/-
**MeasureTheory.integral_concaveOn_of_integrand_ae** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：integral_concaveOn_of_integrand_ae {β : Type*} [AddCommMonoid β] [Module R
eal β] {f : α -> β -> E} {s : Set β} (hs : Convex Real s) (hf_conc : forallᵐ x ∂
μ, ConcaveOn Real s (f x)) (hf_int : forall a in s, Integrable (f · a) μ) : Conc
aveOn Real s (fun b => ∫ x, f x b ∂μ)
参数：hs : Convex Real s；hf_conc : forallᵐ x ∂μ, ConcaveOn Real s (f x)；hf_int : fo
rall a in s, Integrable (f · a) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用引理 `MeasureTheory.integral_convexOn_of_integrand_ae`：integral_convexOn_of_in
tegrand_ae {β : Type*} [AddCommMonoid β] [Module Real β] {f : α -> β -> E} {s : 
Set β} (hs : Convex Real s) (hf_conv …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
lemma integral_concaveOn_of_integrand_ae {β : Type*} [AddCommMonoid β]
    [Module ℝ β] {f : α → β → E} {s : Set β} (hs : Convex ℝ s)
    (hf_conc : ∀ᵐ x ∂μ, ConcaveOn ℝ s (f x)) (hf_int : ∀ a ∈ s, Integrable (f · a) μ) :
    ConcaveOn ℝ s (fun b => ∫ x, f x b ∂μ) := by
  simp_rw [← neg_convexOn_iff] at hf_conc ⊢
  simpa only [Pi.neg_apply, integral_neg] using!
    integral_convexOn_of_integrand_ae hs hf_conc (hf_int · · |>.neg)

end Order

variable [hE : CompleteSpace E]

/-
**MeasureTheory.lintegral_coe_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lintegral_coe_eq_integral (f : α -> Real>=0) (hfi : Integrable (fun x => (
f x : Real)) μ) : ∫⁻ a, f a ∂μ = ENNReal.ofReal (∫ a, f a ∂μ)
参数：f : α -> Real>=0；hfi : Integrable (fun x => (f x : Real)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.enorm_eq`：∀ (x : NNReal), ‖↑x‖ₑ = ↑x
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
-/
theorem lintegral_coe_eq_integral (f : α → ℝ≥0) (hfi : Integrable (fun x => (f x : ℝ)) μ) :
    ∫⁻ a, f a ∂μ = ENNReal.ofReal (∫ a, f a ∂μ) := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (f x).coe_nonneg)
      hfi.aestronglyMeasurable, ← ENNReal.coe_nnreal_eq]
  rw [ENNReal.ofReal_toReal]
  simpa [← lt_top_iff_ne_top, hasFiniteIntegral_iff_enorm, NNReal.enorm_eq] using
    hfi.hasFiniteIntegral
/-
**MeasureTheory.ofReal_integral_eq_lintegral_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：ofReal_integral_eq_lintegral_ofReal {f : α -> Real} (hfi : Integrable f μ)
 (f_nn : 0 <=ᵐ[μ] f) : ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x)
 ∂μ
参数：hfi : Integrable f μ；f_nn : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm`：ofReal_integral_n
orm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α -> P} (hf : Int
egrable f μ) : ENNReal.ofReal (∫ x, ‖f x‖ ∂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem ofReal_integral_eq_lintegral_ofReal {f : α → ℝ} (hfi : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have : f =ᵐ[μ] (‖f ·‖) := f_nn.mono fun _x hx ↦ (abs_of_nonneg hx).symm
  simp_rw [integral_congr_ae this, ofReal_integral_norm_eq_lintegral_enorm hfi,
    ← ofReal_norm]
  exact lintegral_congr_ae (this.symm.fun_comp ENNReal.ofReal)
/-
**MeasureTheory.integral_toReal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_toReal {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hf : forallᵐ
 x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a, f a ∂μ).toReal
参数：hfm : AEMeasurable f μ；hf : forallᵐ x ∂μ, f x < ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.ennreal_toReal`：AEMeasurable.ennreal_toReal {f : α -> Real>
=0∞} {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.to
Real (f x)) μ
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ofReal_toReal_ae_eq`：ofReal_toReal_ae_eq {f : α -> Real>=0
∞} (hf : forallᵐ x ∂μ, f x < ∞) : (fun x => ENNReal.ofReal (f x).toReal) =ᵐ[μ] f
-/
theorem integral_toReal {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) (hf : ∀ᵐ x ∂μ, f x < ∞) :
    ∫ a, (f a).toReal ∂μ = (∫⁻ a, f a ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.ennreal_toReal.aestronglyMeasurable,
    lintegral_congr_ae (ofReal_toReal_ae_eq hf)]
  exact Eventually.of_forall fun x => ENNReal.toReal_nonneg
/-
**MeasureTheory.lintegral_coe_le_coe_iff_integral_le** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：lintegral_coe_le_coe_iff_integral_le {f : α -> Real>=0} (hfi : Integrable 
(fun x => (f x : Real)) μ) {b : Real>=0} : ∫⁻ a, f a ∂μ <= b ↔ ∫ a, (f a : Real)
 ∂μ <= b
参数：hfi : Integrable (fun x => (f x : Real)) μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_coe_eq_integral`：lintegral_coe_eq_integral (f : 
α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ) : ∫⁻ a, f a ∂μ = ENNR
eal.ofReal (∫ a, f a ∂μ)
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Real.toNNReal_le_iff_le_coe`：toNNReal_le_iff_le_coe {r : Real} {p : Real
>=0} : toNNReal r <= p ↔ r <= ↑p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lintegral_coe_le_coe_iff_integral_le {f : α → ℝ≥0} (hfi : Integrable (fun x => (f x : ℝ)) μ)
    {b : ℝ≥0} : ∫⁻ a, f a ∂μ ≤ b ↔ ∫ a, (f a : ℝ) ∂μ ≤ b := by
  rw [lintegral_coe_eq_integral f hfi, ENNReal.ofReal, ENNReal.coe_le_coe,
    Real.toNNReal_le_iff_le_coe]
/-
**MeasureTheory.integral_coe_le_of_lintegral_coe_le** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：integral_coe_le_of_lintegral_coe_le {f : α -> Real>=0} {b : Real>=0} (h : 
∫⁻ a, f a ∂μ <= b) : ∫ a, (f a : Real) ∂μ <= b
参数：h : ∫⁻ a, f a ∂μ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.lintegral_coe_le_coe_iff_integral_le`：lintegral_coe_le_coe
_iff_integral_le {f : α -> Real>=0} (hfi : Integrable (fun x => (f x : Real)) μ)
 {b : Real>=0} : ∫⁻ a, f a ∂μ <= b ↔ ∫ a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem integral_coe_le_of_lintegral_coe_le {f : α → ℝ≥0} {b : ℝ≥0} (h : ∫⁻ a, f a ∂μ ≤ b) :
    ∫ a, (f a : ℝ) ∂μ ≤ b := by
  by_cases hf : Integrable (fun a => (f a : ℝ)) μ
  · exact (lintegral_coe_le_coe_iff_integral_le hf).1 h
  · rw [integral_undef hf]; exact b.2
/-
**MeasureTheory.integral_eq_zero_iff_of_nonneg_ae** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integral_eq_zero_iff_of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi :
 Integrable f μ) : ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0
参数：hf : 0 <=ᵐ[μ] f；hfi : Integrable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_ofReal`：hasFiniteIntegral_iff_ofReal
 {f : α -> Real} (h : 0 <=ᵐ[μ] f) : HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofRea
l (f a) ∂μ) < ∞
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `ENNReal.measurable_ofReal`：measurable_ofReal : Measurable ENNReal.ofReal
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.EventuallyLE.ge_iff_eq'`：∀ {α : Type u} {β : Type v} [inst : Part
ialOrder β] {l : Filter α} {f g : α → β}, g ≤ᶠ[l] f → (f ≤ᶠ[l] g ↔ f =ᶠ[l] g)
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae hf hfi.1, ENNReal.toReal_eq_zero_iff,
    ← ENNReal.not_lt_top, ← hasFiniteIntegral_iff_ofReal hf, hfi.2, not_true_eq_false, or_false]
  rw [lintegral_eq_zero_iff']
  · rw [← hf.ge_iff_eq', Filter.EventuallyEq, Filter.EventuallyLE]
    simp only [Pi.zero_apply, ofReal_eq_zero]
  · exact (ENNReal.measurable_ofReal.comp_aemeasurable hfi.1.aemeasurable)
/-
**MeasureTheory.integral_eq_zero_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：integral_eq_zero_iff_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : Integr
able f μ) : ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0
参数：hf : 0 <= f；hfi : Integrable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_eq_zero_iff_of_nonneg_ae`：integral_eq_zero_iff_of
_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) : ∫ x, f x ∂
μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem integral_eq_zero_iff_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf) hfi
/-
**MeasureTheory.integral_eq_iff_of_ae_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_eq_iff_of_ae_le {f g : α -> Real} (hf : Integrable f μ) (hg : Int
egrable g μ) (hfg : f <=ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ ↔ f =ᵐ[μ] g
参数：hf : Integrable f μ；hg : Integrable g μ；hfg : f <=ᵐ[μ] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.sub_ae_eq_zero`：∀ {α : Type u_2} {m0 : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {β : Type u_7} [inst : AddGroup β]   (f g : α → β)
, f - g =ᵐ[μ] 0 ↔ …
· 使用定理 `MeasureTheory.integral_eq_zero_iff_of_nonneg_ae`：integral_eq_zero_iff_of
_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) : ∫ x, f x ∂
μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.sub_nonneg_ae`：∀ {α : Type u_2} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {β : Type u_7} [inst : AddGroup β]   [inst_1 : LE β
] [AddRightMono β…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
-/
lemma integral_eq_iff_of_ae_le {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    ∫ a, f a ∂μ = ∫ a, g a ∂μ ↔ f =ᵐ[μ] g := by
  refine ⟨fun h_le ↦ EventuallyEq.symm ?_, fun h ↦ integral_congr_ae h⟩
  rw [← sub_ae_eq_zero,
    ← integral_eq_zero_iff_of_nonneg_ae ((sub_nonneg_ae _ _).mpr hfg) (hg.sub hf)]
  simpa [Pi.sub_apply, integral_sub hg hf, sub_eq_zero, eq_comm]
/-
**MeasureTheory.integral_pos_iff_support_of_nonneg_ae** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：integral_pos_iff_support_of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (h
fi : Integrable f μ) : (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f)
参数：hf : 0 <=ᵐ[μ] f；hfi : Integrable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MeasureTheory.integral_eq_zero_iff_of_nonneg_ae`：integral_eq_zero_iff_of
_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) : ∫ x, f x ∂
μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f) := by
  simp_rw [(integral_nonneg_of_ae hf).lt_iff_ne, pos_iff_ne_zero, Ne, @eq_comm ℝ 0,
    integral_eq_zero_iff_of_nonneg_ae hf hfi, Filter.EventuallyEq, ae_iff, Pi.zero_apply,
    Function.support]
/-
**MeasureTheory.integral_pos_iff_support_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：integral_pos_iff_support_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : In
tegrable f μ) : (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f)
参数：hf : 0 <= f；hfi : Integrable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_pos_iff_support_of_nonneg_ae`：integral_pos_iff_su
pport_of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) : (0
 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem integral_pos_iff_support_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) :
    (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f) :=
  integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hf) hfi
/-
**MeasureTheory.integral_exp_pos** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_exp_pos {μ : Measure α} {f : α -> Real} [hμ : NeZero μ] (hf : Int
egrable (fun x => Real.exp (f x)) μ) : 0 < ∫ x, Real.exp (f x) ∂μ
参数：hf : Integrable (fun x => Real.exp (f x)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_pos_iff_support_of_nonneg`：integral_pos_iff_suppo
rt_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ) : (0 < ∫ x, f 
x ∂μ) ↔ 0 < μ (Function.support f)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
lemma integral_exp_pos {μ : Measure α} {f : α → ℝ} [hμ : NeZero μ]
    (hf : Integrable (fun x ↦ Real.exp (f x)) μ) :
    0 < ∫ x, Real.exp (f x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x ↦ (Real.exp_pos _).le) hf]
  suffices (Function.support fun x ↦ Real.exp (f x)) = Set.univ by simp [this, hμ.out]
  ext1 x
  simp only [Function.mem_support, ne_eq, (Real.exp_pos _).ne', not_false_eq_true, Set.mem_univ]

/-- Monotone convergence theorem for real-valued functions and Bochner integrals -/
/-
**MeasureTheory.integral_tendsto_of_tendsto_of_monotone** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：integral_tendsto_of_tendsto_of_monotone {μ : Measure α} {f : Nat -> α -> R
eal} {F : α -> Real} (hf : forall n, Integrable (f n) μ) (hF : Integrable F μ) (
h_mono : forallᵐ x ∂μ, Monotone fun n => f n x) (h_tendsto : forallᵐ x ∂μ, Tends
to (fun n => f n x) atTop (𝓝 (F x))) : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝
 (∫ x, F x ∂μ))
参数：hf : forall n, Integrable (f n) μ；hF : Integrable F μ；h_mono : forallᵐ x ∂μ, 
Monotone fun n => f n x；h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop
 (𝓝 (F x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用引理 `ENNReal.continuousAt_toReal`：continuousAt_toReal (hx : x != ∞) : Continu
ousAt ENNReal.toReal x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Monotone convergence theorem for real-valued functions and Bochner integrals
-/
lemma integral_tendsto_of_tendsto_of_monotone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  -- switch from the Bochner to the Lebesgue integral
  let f' := fun n x ↦ f n x - f 0 x
  have hf'_nonneg : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f' n x := by
    filter_upwards [h_mono] with a ha n
    simp [f', ha zero_le]
  have hf'_meas : ∀ n, Integrable (f' n) μ := fun n ↦ (hf n).sub (hf 0)
  suffices Tendsto (fun n ↦ ∫ x, f' n x ∂μ) atTop (𝓝 (∫ x, (F - f 0) x ∂μ)) by
    simp_rw [f', integral_sub (hf _) (hf _), integral_sub' hF (hf 0),
      tendsto_sub_const_iff] at this
    exact this
  have hF_ge : 0 ≤ᵐ[μ] fun x ↦ (F - f 0) x := by
    filter_upwards [h_tendsto, h_mono] with x hx_tendsto hx_mono
    simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    exact ge_of_tendsto' hx_tendsto (fun n ↦ hx_mono zero_le)
  rw [ae_all_iff] at hf'_nonneg
  simp_rw [integral_eq_lintegral_of_nonneg_ae (hf'_nonneg _) (hf'_meas _).1]
  rw [integral_eq_lintegral_of_nonneg_ae hF_ge (hF.1.sub (hf 0).1)]
  have h_cont := ENNReal.continuousAt_toReal (x := ∫⁻ a, ENNReal.ofReal ((F - f 0) a) ∂μ) ?_
  swap
  · rw [← ofReal_integral_eq_lintegral_ofReal (hF.sub (hf 0)) hF_ge]
    finiteness
  refine h_cont.tendsto.comp ?_
  -- use the result for the Lebesgue integral
  refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
  · exact fun n ↦ ((hf n).sub (hf 0)).aemeasurable.ennreal_ofReal
  · filter_upwards [h_mono] with x hx n m hnm
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [f', tsub_le_iff_right, sub_add_cancel]
    exact hx hnm
  · filter_upwards [h_tendsto] with x hx
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simp only [Pi.sub_apply]
    exact Tendsto.sub hx tendsto_const_nhds

/-- Monotone convergence theorem for real-valued functions and Bochner integrals -/
/-
**MeasureTheory.integral_tendsto_of_tendsto_of_antitone** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：integral_tendsto_of_tendsto_of_antitone {μ : Measure α} {f : Nat -> α -> R
eal} {F : α -> Real} (hf : forall n, Integrable (f n) μ) (hF : Integrable F μ) (
h_mono : forallᵐ x ∂μ, Antitone fun n => f n x) (h_tendsto : forallᵐ x ∂μ, Tends
to (fun n => f n x) atTop (𝓝 (F x))) : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝
 (∫ x, F x ∂μ))
参数：hf : forall n, Integrable (f n) μ；hF : Integrable F μ；h_mono : forallᵐ x ∂μ, 
Antitone fun n => f n x；h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop
 (𝓝 (F x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_tendsto_of_tendsto_of_monotone`：integral_tendsto_
of_tendsto_of_monotone {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real} (h
f : forall n, Integrable (f n) μ) (hF : Int…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
Monotone convergence theorem for real-valued functions and Bochner integrals
-/
lemma integral_tendsto_of_tendsto_of_antitone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  suffices Tendsto (fun n ↦ ∫ x, -f n x ∂μ) atTop (𝓝 (∫ x, -F x ∂μ)) by
    suffices Tendsto (fun n ↦ ∫ x, - -f n x ∂μ) atTop (𝓝 (∫ x, - -F x ∂μ)) by
      simpa [neg_neg] using this
    convert! this.neg <;> rw [integral_neg]
  refine integral_tendsto_of_tendsto_of_monotone (fun n ↦ (hf n).neg) hF.neg ?_ ?_
  · filter_upwards [h_mono] with x hx n m hnm using neg_le_neg_iff.mpr <| hx hnm
  · filter_upwards [h_tendsto] with x hx using hx.neg

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. -/
/-
**MeasureTheory.tendsto_of_integral_tendsto_of_monotone** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendsto_of_integral_tendsto_of_monotone {μ : Measure α} {f : Nat -> α -> R
eal} {F : α -> Real} (hf_int : forall n, Integrable (f n) μ) (hF_int : Integrabl
e F μ) (hf_tendsto : Tendsto (fun i => ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ))) (
hf_mono : forallᵐ a ∂μ, Monotone (fun i => f i a)) (hf_bound : forallᵐ a ∂μ, for
all i, f i a <= F a) : forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F a))
参数：hf_int : forall n, Integrable (f n) μ；hF_int : Integrable F μ；hf_tendsto : Te
ndsto (fun i => ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ))；hf_mono : forallᵐ a ∂μ, M
onotone (fun i => f i a)；hf_bound : forallᵐ a ∂μ, forall i, f i a <= F a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_ofReal`：continuous_ofReal : Continuous ENNReal.ofReal
· 使用定理 `Filter.tendsto_sub_const_iff`：∀ {α : Type u} {G : Type u_1} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [ContinuousSub G] (b : G) {c : G}   {f : α
 → G} {l : Filter …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用引理 `MeasureTheory.tendsto_of_lintegral_tendsto_of_monotone`：tendsto_of_linte
gral_tendsto_of_monotone {α : Type*} {mα : MeasurableSpace α} {f : Nat -> α -> R
eal>=0∞} {F : α -> Real>=0∞} {μ : Measure α}…
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `AEMeasurable.sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSpac
e G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   {μ : MeasureTheory
.Measu…
· 使用定理 `ContinuousSub.measurableSub₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Sub γ] [Con…
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If a monotone sequence of functions has an upper bound and the sequence of integ
rals of these
functions tends to the integral of the upper bound, then the sequence of functio
ns converges
almost everywhere to the upper bound.
-/
lemma tendsto_of_integral_tendsto_of_monotone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf_int : ∀ n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f i a))
    (hf_bound : ∀ᵐ a ∂μ, ∀ i, f i a ≤ F a) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  -- reduce to the `ℝ≥0∞` case
  let f' : ℕ → α → ℝ≥0∞ := fun n a ↦ ENNReal.ofReal (f n a - f 0 a)
  let F' : α → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (F a - f 0 a)
  have hf'_int_eq : ∀ i, ∫⁻ a, f' i a ∂μ = ENNReal.ofReal (∫ a, f i a ∂μ - ∫ a, f 0 a ∂μ) := by
    intro i
    unfold f'
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_sub (hf_int i) (hf_int 0)]
    · exact (hf_int i).sub (hf_int 0)
    · filter_upwards [hf_mono] with a h_mono
      simp [h_mono zero_le]
  have hF'_int_eq : ∫⁻ a, F' a ∂μ = ENNReal.ofReal (∫ a, F a ∂μ - ∫ a, f 0 a ∂μ) := by
    unfold F'
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_sub hF_int (hf_int 0)]
    · exact hF_int.sub (hf_int 0)
    · filter_upwards [hf_bound] with a h_bound
      simp [h_bound 0]
  have h_tendsto : Tendsto (fun i ↦ ∫⁻ a, f' i a ∂μ) atTop (𝓝 (∫⁻ a, F' a ∂μ)) := by
    simp_rw [hf'_int_eq, hF'_int_eq]
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    rwa [tendsto_sub_const_iff]
  have h_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f' i a) := by
    filter_upwards [hf_mono] with a ha_mono i j hij
    refine ENNReal.ofReal_le_ofReal ?_
    simp [ha_mono hij]
  have h_bound : ∀ᵐ a ∂μ, ∀ i, f' i a ≤ F' a := by
    filter_upwards [hf_bound] with a ha_bound i
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [tsub_le_iff_right, sub_add_cancel, ha_bound i]
  -- use the corresponding lemma for `ℝ≥0∞`
  have h := tendsto_of_lintegral_tendsto_of_monotone ?_ h_tendsto h_mono h_bound ?_
  rotate_left
  · exact (hF_int.1.aemeasurable.sub (hf_int 0).1.aemeasurable).ennreal_ofReal
  · exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt (hF_int.sub (hf_int 0)).2).ne
  filter_upwards [h, hf_mono, hf_bound] with a ha ha_mono ha_bound
  have h1 : (fun i ↦ f i a) = fun i ↦ (f' i a).toReal + f 0 a := by
    unfold f'
    ext i
    rw [ENNReal.toReal_ofReal]
    · abel
    · simp [ha_mono zero_le]
  have h2 : F a = (F' a).toReal + f 0 a := by
    unfold F'
    rw [ENNReal.toReal_ofReal]
    · abel
    · simp [ha_bound 0]
  rw [h1, h2]
  refine Filter.Tendsto.add ?_ tendsto_const_nhds
  exact (ENNReal.continuousAt_toReal (by finiteness)).tendsto.comp ha

/-- If an antitone sequence of functions has a lower bound and the sequence of integrals of these
functions tends to the integral of the lower bound, then the sequence of functions converges
almost everywhere to the lower bound. -/
/-
**MeasureTheory.tendsto_of_integral_tendsto_of_antitone** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendsto_of_integral_tendsto_of_antitone {μ : Measure α} {f : Nat -> α -> R
eal} {F : α -> Real} (hf_int : forall n, Integrable (f n) μ) (hF_int : Integrabl
e F μ) (hf_tendsto : Tendsto (fun i => ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ))) (
hf_mono : forallᵐ a ∂μ, Antitone (fun i => f i a)) (hf_bound : forallᵐ a ∂μ, for
all i, F a <= f i a) : forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F a))
参数：hf_int : forall n, Integrable (f n) μ；hF_int : Integrable F μ；hf_tendsto : Te
ndsto (fun i => ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ))；hf_mono : forallᵐ a ∂μ, A
ntitone (fun i => f i a)；hf_bound : forallᵐ a ∂μ, forall i, F a <= f i a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.tendsto_of_integral_tendsto_of_monotone`：tendsto_of_integr
al_tendsto_of_monotone {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real} (h
f_int : forall n, Integrable (f n) μ) (hF_i…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If an antitone sequence of functions has a lower bound and the sequence of integ
rals of these
functions tends to the integral of the lower bound, then the sequence of functio
ns converges
almost everywhere to the lower bound.
-/
lemma tendsto_of_integral_tendsto_of_antitone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf_int : ∀ n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Antitone (fun i ↦ f i a))
    (hf_bound : ∀ᵐ a ∂μ, ∀ i, F a ≤ f i a) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  let f' : ℕ → α → ℝ := fun i a ↦ - f i a
  let F' : α → ℝ := fun a ↦ - F a
  suffices ∀ᵐ a ∂μ, Tendsto (fun i ↦ f' i a) atTop (𝓝 (F' a)) by
    filter_upwards [this] with a ha_tendsto
    convert! ha_tendsto.neg
    · simp [f']
    · simp [F']
  refine tendsto_of_integral_tendsto_of_monotone (fun n ↦ (hf_int n).neg) hF_int.neg ?_ ?_ ?_
  · convert! hf_tendsto.neg
    · rw [integral_neg]
    · rw [integral_neg]
  · filter_upwards [hf_mono] with a ha i j hij
    simp [f', ha hij]
  · filter_upwards [hf_bound] with a ha i
    simp [f', F', ha i]

section NormedAddCommGroup

variable {H : Type*} [NormedAddCommGroup H]

/-
**MeasureTheory.L1.norm_eq_integral_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.L1`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {H 
: Type u_6} [inst : NormedAddCommGroup H]   (f : ↥(MeasureTheory.Lp H 1 μ)), ‖f‖
 = ∫ (a : α), ‖↑↑f a‖ ∂μ
参数：f : ↥(MeasureTheory.Lp H 1 μ)；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem L1.norm_eq_integral_norm (f : α →₁[μ] H) : ‖f‖ = ∫ a, ‖f a‖ ∂μ := by
  simp only [eLpNorm, eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_one, ENNReal.rpow_one,
    Lp.norm_def, if_false, ENNReal.one_ne_top, one_ne_zero, _root_.div_one]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (by simp [norm_nonneg]))
      (Lp.aestronglyMeasurable f).norm]
  simp
/-
**MeasureTheory.L1.dist_eq_integral_dist** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.L1`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {H 
: Type u_6} [inst : NormedAddCommGroup H]   (f g : ↥(MeasureTheory.Lp H 1 μ)), d
ist f g = ∫ (a : α), dist (↑↑f a) (↑↑g a) ∂μ
参数：f g : ↥(MeasureTheory.Lp H 1 μ)；a : α；↑↑f a；↑↑g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `MeasureTheory.L1.norm_eq_integral_norm`：∀ {α : Type u_1} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} {H : Type u_6} [inst : NormedAddCommGroup
 H]   (f : ↥(MeasureTheory.L…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
-/
theorem L1.dist_eq_integral_dist (f g : α →₁[μ] H) : dist f g = ∫ a, dist (f a) (g a) ∂μ := by
  simp only [dist_eq_norm, L1.norm_eq_integral_norm]
  exact integral_congr_ae <| (Lp.coeFn_sub _ _).fun_comp norm
/-
**MeasureTheory.L1.norm_of_fun_eq_integral_norm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.L1`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {H 
: Type u_6} [inst : NormedAddCommGroup H]   {f : α → H} (hf : MeasureTheory.Inte
grable f μ), ‖MeasureTheory.Integrable.toL1 f hf‖ = ∫ (a : α), ‖f a‖ ∂μ
参数：hf : MeasureTheory.Integrable f μ；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.norm_eq_integral_norm`：∀ {α : Type u_1} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} {H : Type u_6} [inst : NormedAddCommGroup
 H]   (f : ↥(MeasureTheory.L…
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.coeFn_toL1`：coeFn_toL1 {f : α -> β} (hf : Integ
rable f μ) : hf.toL1 f =ᵐ[μ] f
-/
theorem L1.norm_of_fun_eq_integral_norm {f : α → H} (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ∫ a, ‖f a‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae <| hf.coeFn_toL1.fun_comp _
/-
**MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {H 
: Type u_6} [inst : NormedAddCommGroup H]   {f : α → H} {p : ENNReal},   p ≠ 0 →
     p ≠ ⊤ →       MeasureTheory.MemLp f p μ →         MeasureTheory.eLpNorm f p
 μ = ENNReal.ofReal ((∫ (a : α), ‖f a‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹)
参数：(∫ (a : α), ‖f a‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_rpow_of_nonneg`：ofReal_rpow_of_nonneg {x p : Real} (hx_no
nneg : 0 <= x) (hp_nonneg : 0 <= p) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^
 p)
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 34 条，此处仅展示前 30 条）
-/
theorem MemLp.eLpNorm_eq_integral_rpow_norm {f : α → H} {p : ℝ≥0∞} (hp1 : p ≠ 0) (hp2 : p ≠ ∞)
    (hf : MemLp f p μ) :
    eLpNorm f p μ = ENNReal.ofReal ((∫ a, ‖f a‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) := by
  have A : ∫⁻ a : α, ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ = ∫⁻ a : α, ‖f a‖ₑ ^ p.toReal ∂μ := by
    simp_rw [← ofReal_rpow_of_nonneg (norm_nonneg _) toReal_nonneg, ofReal_norm]
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 hp2, one_div]
  rw [integral_eq_lintegral_of_nonneg_ae]; rotate_left
  · exact ae_of_all _ fun x => by positivity
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [A, ← ofReal_rpow_of_nonneg toReal_nonneg (inv_nonneg.2 toReal_nonneg), ofReal_toReal]
  exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp1 hp2 hf.2).ne

end NormedAddCommGroup

/-
**MeasureTheory.norm_integral_le_integral_norm** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：norm_integral_le_integral_norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ 
∂μ
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.norm_integral_le_lintegral_norm`：norm_integral_le_lintegra
l_norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a
‖ ∂μ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_non_aestronglyMeasurable`：integral_non_aestrongly
Measurable {f : α -> G} (h : ¬AEStronglyMeasurable f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem norm_integral_le_integral_norm (f : α → G) : ‖∫ a, f a ∂μ‖ ≤ ∫ a, ‖f a‖ ∂μ := by
  have le_ae : ∀ᵐ a ∂μ, 0 ≤ ‖f a‖ := Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ
  · calc
      ‖∫ a, f a ∂μ‖ ≤ ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) :=
        norm_integral_le_lintegral_norm _
      _ = ∫ a, ‖f a‖ ∂μ := (integral_eq_lintegral_of_nonneg_ae le_ae <| h.norm).symm
  · rw [integral_non_aestronglyMeasurable h, norm_zero]
    exact integral_nonneg_of_ae le_ae
/-
**MeasureTheory.abs_integral_le_integral_abs** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：abs_integral_le_integral_abs {f : α -> Real} : |∫ a, f a ∂μ| <= ∫ a, |f a|
 ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
-/
lemma abs_integral_le_integral_abs {f : α → ℝ} : |∫ a, f a ∂μ| ≤ ∫ a, |f a| ∂μ :=
  norm_integral_le_integral_norm f
/-
**MeasureTheory.norm_integral_le_of_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：norm_integral_le_of_norm_le {f : α -> G} {g : α -> Real} (hg : Integrable 
g μ) (h : forallᵐ x ∂μ, ‖f x‖ <= g x) : ‖∫ x, f x ∂μ‖ <= ∫ x, g x ∂μ
参数：hg : Integrable g μ；h : forallᵐ x ∂μ, ‖f x‖ <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用引理 `MeasureTheory.integral_mono_of_nonneg`：integral_mono_of_nonneg {f g : α 
-> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ a, f a ∂μ <=
 ∫ a, g a ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_integral_le_of_norm_le {f : α → G} {g : α → ℝ} (hg : Integrable g μ)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) : ‖∫ x, f x ∂μ‖ ≤ ∫ x, g x ∂μ :=
  calc
    ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm f
    _ ≤ ∫ x, g x ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hg h

@[simp]
/-
**MeasureTheory.integral_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_const (c : E) : ∫ _ : α, c ∂μ = μ.real univ • c
参数：c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_const`：setToFun_const [CompleteSpace F] [IsFinite
Measure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E) : (setToFun μ T hT fun 
_ => x) = T univ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `MeasureTheory.integrable_const_iff_isFiniteMeasure`：integrable_const_iff
_isFiniteMeasure {c : β} (hc : c != 0) : Integrable (fun _ => c) μ ↔ IsFiniteMea
sure μ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.not_isFiniteMeasure_iff`：not_isFiniteMeasure_iff : ¬IsFini
teMeasure μ ↔ μ univ = ∞
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem integral_const (c : E) : ∫ _ : α, c ∂μ = μ.real univ • c := by
  by_cases hμ : IsFiniteMeasure μ
  · simp only [integral_eq_setToFun]
    exact setToFun_const (dominatedFinMeasAdditive_weightedSMul _) _
  by_cases hc : c = 0
  · simp [hc, integral_zero]
  · simp [measureReal_def, (integrable_const_iff_isFiniteMeasure hc).not.2 hμ,
      integral_undef, MeasureTheory.not_isFiniteMeasure_iff.mp hμ]
/-
**MeasureTheory.integral_eq_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_eq_const [IsProbabilityMeasure μ] {f : α -> E} {c : E} (hf : fora
llᵐ x ∂μ, f x = c) : ∫ x, f x ∂μ = c
参数：hf : forallᵐ x ∂μ, f x = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_eq_const [IsProbabilityMeasure μ] {f : α → E} {c : E} (hf : ∀ᵐ x ∂μ, f x = c) :
    ∫ x, f x ∂μ = c := by simp [integral_congr_ae hf]
/-
**MeasureTheory.norm_integral_le_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：norm_integral_le_of_norm_le_const [IsFiniteMeasure μ] {f : α -> G} {C : Re
al} (h : forallᵐ x ∂μ, ‖f x‖ <= C) : ‖∫ x, f x ∂μ‖ <= C * μ.real univ
参数：h : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.norm_integral_le_of_norm_le`：norm_integral_le_of_norm_le {
f : α -> G} {g : α -> Real} (hg : Integrable g μ) (h : forallᵐ x ∂μ, ‖f x‖ <= g 
x) : ‖∫ x, f x ∂μ‖ <= ∫ x, g x …
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem norm_integral_le_of_norm_le_const [IsFiniteMeasure μ] {f : α → G} {C : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖∫ x, f x ∂μ‖ ≤ C * μ.real univ :=
  calc
    ‖∫ x, f x ∂μ‖ ≤ ∫ _, C ∂μ := norm_integral_le_of_norm_le (integrable_const C) h
    _ = C * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

variable {ν : Measure α}
/-
**MeasureTheory.integral_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_add_measure {f : α -> G} (hμ : Integrable f μ) (hν : Integrable f
 ν) : ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν
参数：hμ : Integrable f μ；hν : Integrable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_add_left''`：setToFun_add_left'' {hT : DominatedFi
nMeasAdditive μ T C} {hT' : DominatedFinMeasAdditive μ' T' C'} {hT'' : Dominated
FinMeasAdditive μ'' T''…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem integral_add_measure {f : α → G} (hμ : Integrable f μ) (hν : Integrable f ν) :
    ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν := by
  simp only [integral_eq_setToFun]
  apply setToFun_add_left'' (fun s hs h's ↦ ?_) hμ hν le_rfl zero_le_one zero_le_one zero_le_one
  simp only [Measure.coe_add, Pi.add_apply, add_lt_top] at h's
  simp [weightedSMul, Measure.real, toReal_add, h's.1.ne, h's.2.ne, add_smul]

@[simp]
/-
**MeasureTheory.integral_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_zero_measure {m : MeasurableSpace α} (f : α -> G) : (∫ x, f x ∂(0
 : Measure α)) = 0
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_measure_zero`：setToFun_measure_zero (hT : Dominat
edFinMeasAdditive μ T C) (h : μ = 0) : setToFun μ T hT f = 0
-/
theorem integral_zero_measure {m : MeasurableSpace α} (f : α → G) :
    (∫ x, f x ∂(0 : Measure α)) = 0 := by
  simp only [integral_eq_setToFun]
  exact setToFun_measure_zero (dominatedFinMeasAdditive_weightedSMul _) rfl

@[simp]
/-
**MeasureTheory.setIntegral_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setIntegral_measure_zero (f : α -> G) {μ : Measure α} {s : Set α} (hs : μ 
s = 0) : ∫ x in s, f x ∂μ = 0
参数：f : α -> G；hs : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
-/
theorem setIntegral_measure_zero (f : α → G) {μ : Measure α} {s : Set α} (hs : μ s = 0) :
    ∫ x in s, f x ∂μ = 0 := Measure.restrict_eq_zero.mpr hs ▸ integral_zero_measure f
/-
**MeasureTheory.integral_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_of_isEmpty [IsEmpty α] {f : α -> G} : ∫ x, f x ∂μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.eq_zero_of_isEmpty`：eq_zero_of_isEmpty [IsEmpty α]
 {_m : MeasurableSpace α} (μ : Measure α) : μ = 0
-/
lemma integral_of_isEmpty [IsEmpty α] {f : α → G} : ∫ x, f x ∂μ = 0 :=
  μ.eq_zero_of_isEmpty ▸ integral_zero_measure _
/-
**MeasureTheory.integral_finsetSum_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integral_finsetSum_measure {ι} {m : MeasurableSpace α} {f : α -> G} {μ : ι
 -> Measure α} {s : Finset ι} (hf : forall i in s, Integrable f (μ i)) : ∫ a, f 
a ∂(∑ i in s, μ i) = ∑ i in s, ∫ a, f a ∂μ i
参数：hf : forall i in s, Integrable f (μ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `MeasureTheory.integral_add_measure`：integral_add_measure {f : α -> G} (h
μ : Integrable f μ) (hν : Integrable f ν) : ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ 
x, f x ∂ν
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_finsetSum_measure`：integrable_finsetSum_measure
 [PseudoMetrizableSpace ε] {ι} {m : MeasurableSpace α} {f : α -> ε} {μ : ι -> Me
asure α} {s : Finset ι} : Integr…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
theorem integral_finsetSum_measure {ι} {m : MeasurableSpace α} {f : α → G} {μ : ι → Measure α}
    {s : Finset ι} (hf : ∀ i ∈ s, Integrable f (μ i)) :
    ∫ a, f a ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫ a, f a ∂μ i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ h ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons, Finset.sum_cons, ← ih hf.2]
    exact integral_add_measure hf.1 (integrable_finsetSum_measure.2 hf.2)

@[deprecated (since := "2026-04-08")]
alias integral_finset_sum_measure := integral_finsetSum_measure
/-
**MeasureTheory.nndist_integral_add_measure_le_lintegral** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：nndist_integral_add_measure_le_lintegral {f : α -> G} (h₁ : Integrable f μ
) (h₂ : Integrable f ν) : (nndist (∫ x, f x ∂μ) (∫ x, f x ∂(μ + ν)) : Real>=0∞) 
<= ∫⁻ x, ‖f x‖ₑ ∂ν
参数：h₁ : Integrable f μ；h₂ : Integrable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_add_measure`：integral_add_measure {f : α -> G} (h
μ : Integrable f μ) (hν : Integrable f ν) : ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ 
x, f x ∂ν
· 使用定理 `nndist_comm`：nndist_comm (x y : α) : nndist x y = nndist y x
· 使用定理 `nndist_eq_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), nndist a b = ‖a - b‖₊
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `MeasureTheory.enorm_integral_le_lintegral_enorm`：enorm_integral_le_linte
gral_enorm (f : α -> G) : ‖∫ a, f a ∂μ‖ₑ <= ∫⁻ a, ‖f a‖ₑ ∂μ
-/
theorem nndist_integral_add_measure_le_lintegral
    {f : α → G} (h₁ : Integrable f μ) (h₂ : Integrable f ν) :
    (nndist (∫ x, f x ∂μ) (∫ x, f x ∂(μ + ν)) : ℝ≥0∞) ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := by
  rw [integral_add_measure h₁ h₂, nndist_comm, nndist_eq_nnnorm, add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm _

@[simp]
/-
**MeasureTheory.integral_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_smul_measure (f : α -> G) (c : Real>=0∞) : ∫ x, f x ∂c • μ = c.to
Real • ∫ x, f x ∂μ
参数：f : α -> G；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_top`：⊤.toReal = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_top_smul_measure`：setToFun_top_smul_measure (hT :
 DominatedFinMeasAdditive (∞ • μ) T C) (f : α -> E) : setToFun (∞ • μ) T hT f = 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.smul`：smul [SeminormedAddGroup 𝕜]
 [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β] (hT : DominatedFinMeasAdditive μ T C) (c 
: 𝕜) : DominatedFinMeasAdditive μ…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.of_smul_measure`：of_smul_measure 
{c : Real>=0∞} (hc_ne_top : c != ∞) (hT : DominatedFinMeasAdditive (c • μ) T C) 
: DominatedFinMeasAdditive μ T (c.toReal * C…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.setToFun_congr_smul_measure`：setToFun_congr_smul_measure (
c : Real>=0∞) (hc_ne_top : c != ∞) (hT : DominatedFinMeasAdditive μ T C) (hT_smu
l : DominatedFinMeasAdditive (c…
· 使用定理 `MeasureTheory.setToFun_congr_left'`：setToFun_congr_left' (hT : Dominated
FinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (h : forall s, M
easurableSet s -> μ s < …
· 使用定理 `MeasureTheory.weightedSMul_smul_measure`：weightedSMul_smul_measure {m : 
MeasurableSpace α} (μ : Measure α) (c : Real>=0∞) {s : Set α} : (weightedSMul (c
 • μ) s : F ->L[Real] F) = c.…
-/
theorem integral_smul_measure (f : α → G) (c : ℝ≥0∞) :
    ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ := by
  -- First we consider the “degenerate” case `c = ∞`
  rcases eq_or_ne c ∞ with (rfl | hc)
  · rw [ENNReal.toReal_top, zero_smul, integral_eq_setToFun, setToFun_top_smul_measure]
  -- Main case: `c ≠ ∞`
  simp_rw [integral_eq_setToFun, ← setToFun_smul_left]
  have hdfma : DominatedFinMeasAdditive μ (weightedSMul (c • μ) : Set α → G →L[ℝ] G) c.toReal :=
    mul_one c.toReal ▸ (dominatedFinMeasAdditive_weightedSMul (c • μ)).of_smul_measure hc
  have hdfma_smul := dominatedFinMeasAdditive_weightedSMul (F := G) (c • μ)
  rw [← setToFun_congr_smul_measure c hc hdfma hdfma_smul f]
  exact setToFun_congr_left' _ _ (fun s _ _ => weightedSMul_smul_measure μ c) f

@[simp]
/-
**MeasureTheory.integral_smul_nnreal_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_smul_nnreal_measure (f : α -> G) (c : Real>=0) : ∫ x, f x ∂(c • μ
) = c • ∫ x, f x ∂μ
参数：f : α -> G；c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
-/
theorem integral_smul_nnreal_measure (f : α → G) (c : ℝ≥0) :
    ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ :=
  integral_smul_measure f (c : ℝ≥0∞)
/-
**MeasureTheory.integral_map_of_stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：integral_map_of_stronglyMeasurable {β} [MeasurableSpace β] {φ : α -> β} (h
φ : Measurable φ) {f : β -> G} (hfm : StronglyMeasurable f) : ∫ y, f y ∂Measure.
map φ μ = ∫ x, f (φ x) ∂μ
参数：hφ : Measurable φ；hfm : StronglyMeasurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.setToFun_of_le_map_of_stronglyMeasurable`：setToFun_of_le_m
ap_of_stronglyMeasurable (hT : DominatedFinMeasAdditive μ T C) {β : Type*} {_ : 
MeasurableSpace β} {μ' : Measure β} {φ : α -…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.weightedSMul_apply`：weightedSMul_apply {m : MeasurableSpac
e α} (μ : Measure α) (s : Set α) (x : F) : weightedSMul μ s x = μ.real s • x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.map_measureReal_apply`：map_measureReal_apply [MeasurableSp
ace β] {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : (μ.
map f).real s = μ.real (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem integral_map_of_stronglyMeasurable {β} [MeasurableSpace β] {φ : α → β} (hφ : Measurable φ)
    {f : β → G} (hfm : StronglyMeasurable f) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ := by
  by_cases hfi : Integrable f (Measure.map φ μ); swap
  · rw [integral_undef hfi, integral_undef]
    exact fun hfφ => hfi ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hfφ)
  simp only [integral_eq_setToFun]
  apply setToFun_of_le_map_of_stronglyMeasurable _ _
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).1 hfi) hfm hφ le_rfl
  intro s x hs
  simp [weightedSMul_apply, map_measureReal_apply, hs, hφ]
/-
**MeasureTheory.integral_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_map {β} [MeasurableSpace β] {φ : α -> β} (hφ : AEMeasurable φ μ) 
{f : β -> G} (hfm : AEStronglyMeasurable f (Measure.map φ μ)) : ∫ y, f y ∂Measur
e.map φ μ = ∫ x, f (φ x) ∂μ
参数：hφ : AEMeasurable φ μ；hfm : AEStronglyMeasurable f (Measure.map φ μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.integral_map_of_stronglyMeasurable`：integral_map_of_strong
lyMeasurable {β} [MeasurableSpace β] {φ : α -> β} (hφ : Measurable φ) {f : β -> 
G} (hfm : StronglyMeasurable f) : ∫ y,…
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_comp`：ae_eq_comp {f : α -> β} {g g' : β -> δ} (hf : 
AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') : g ∘ f =ᵐ[μ] g' ∘ f
-/
theorem integral_map {β} [MeasurableSpace β] {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → G}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  let g := hfm.mk f
  calc
    ∫ y, f y ∂Measure.map φ μ = ∫ y, g y ∂Measure.map φ μ := integral_congr_ae hfm.ae_eq_mk
    _ = ∫ y, g y ∂Measure.map (hφ.mk φ) μ := by congr 1; exact Measure.map_congr hφ.ae_eq_mk
    _ = ∫ x, g (hφ.mk φ x) ∂μ :=
      (integral_map_of_stronglyMeasurable hφ.measurable_mk hfm.stronglyMeasurable_mk)
    _ = ∫ x, g (φ x) ∂μ := integral_congr_ae (hφ.ae_eq_mk.symm.fun_comp _)
    _ = ∫ x, f (φ x) ∂μ := integral_congr_ae <| ae_eq_comp hφ hfm.ae_eq_mk.symm
/-
**MeasureTheory._root_.MeasurableEmbedding.integral_map** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.integral_map {β} {_ : MeasurableSpace β} {f : α → β}
    (hf : MeasurableEmbedding f) (g : β → G) : ∫ y, g y ∂Measure.map f μ = ∫ x, g (f x) ∂μ := by
  by_cases hgm : AEStronglyMeasurable g (Measure.map f μ)
  · exact MeasureTheory.integral_map hf.measurable.aemeasurable hgm
  · rw [integral_non_aestronglyMeasurable hgm, integral_non_aestronglyMeasurable]
    exact fun hgf => hgm (hf.aestronglyMeasurable_map_iff.2 hgf)
/-
**MeasureTheory._root_.Topology.IsClosedEmbedding.integral_map** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Topology.IsClosedEmbedding.integral_map {β} [TopologicalSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {φ : α → β} (hφ : IsClosedEmbedding φ)
    (f : β → G) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  hφ.measurableEmbedding.integral_map _
/-
**MeasureTheory.integral_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y
, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
参数：e : α ≃ᵐ β；f : β -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.integral_map`：∀ {α : Type u_1} {G : Type u_5} [inst 
: NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ 
: MeasureTheory.Measur…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β → G) :
    ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ :=
  e.measurableEmbedding.integral_map f

omit hE in
/-
**MeasureTheory.integral_domSMul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulActio
n G A] [MeasurableSpace A] [MeasurableConstSMul G A] {μ : Measure A} (g : Gᵈᵐᵃ) 
(f : A -> E) : ∫ x, f x ∂g • μ = ∫ x, f ((DomMulAct.mk.symm g)⁻¹ • x) ∂μ
参数：g : Gᵈᵐᵃ；f : A -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma integral_domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [MeasurableSpace A] [MeasurableConstSMul G A] {μ : Measure A} (g : Gᵈᵐᵃ) (f : A → E) :
    ∫ x, f x ∂g • μ = ∫ x, f ((DomMulAct.mk.symm g)⁻¹ • x) ∂μ :=
  integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f
/-
**MeasureTheory.MeasurePreserving.integral_comp** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : No
rmedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {β : Type
 u_6} {x : MeasurableSpace β} {f : α → β} {ν : MeasureTheory.Measure β},   Measu
reTheory.MeasurePreserving f μ ν →     MeasurableEmbedding f → ∀ (g : β → G), ∫ 
(x : α), g (f x) ∂μ = ∫ (y : β), g y ∂ν
参数：g : β → G；x : α；f x；y : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.integral_map`：∀ {α : Type u_1} {G : Type u_5} [inst 
: NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ 
: MeasureTheory.Measur…
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
theorem MeasurePreserving.integral_comp {β} {_ : MeasurableSpace β} {f : α → β} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν :=
  h₁.map_eq ▸ (h₂.integral_map g).symm
/-
**MeasureTheory.MeasurePreserving.integral_comp'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : No
rmedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {β : Type
 u_6} [inst_2 : MeasurableSpace β] {ν : MeasureTheory.Measure β} {f : α ≃ᵐ β},  
 MeasureTheory.MeasurePreserving (⇑f) μ ν → ∀ (g : β → G), ∫ (x : α), g (f x) ∂μ
 = ∫ (y : β), g y ∂ν
参数：⇑f；g : β → G；x : α；f x；y : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem MeasurePreserving.integral_comp' {β} [MeasurableSpace β] {ν} {f : α ≃ᵐ β}
    (h : MeasurePreserving f μ ν) (g : β → G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := MeasurePreserving.integral_comp h f.measurableEmbedding _
/-
**MeasureTheory.integral_subtype_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integral_subtype_comap {α} [MeasurableSpace α] {μ : Measure α} {s : Set α}
 (hs : MeasurableSet s) (f : α -> G) : ∫ x : s, f (x : α) ∂(Measure.comap Subtyp
e.val μ) = ∫ x in s, f x ∂μ
参数：hs : MeasurableSet s；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
· 使用定理 `MeasurableEmbedding.integral_map`：∀ {α : Type u_1} {G : Type u_5} [inst 
: NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ 
: MeasureTheory.Measur…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
-/
theorem integral_subtype_comap {α} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : α → G) :
    ∫ x : s, f (x : α) ∂(Measure.comap Subtype.val μ) = ∫ x in s, f x ∂μ := by
  rw [← map_comap_subtype_coe hs]
  exact ((MeasurableEmbedding.subtype_coe hs).integral_map _).symm

attribute [local instance] Measure.Subtype.measureSpace in
/-
**MeasureTheory.integral_subtype** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_subtype {α} [MeasureSpace α] {s : Set α} (hs : MeasurableSet s) (
f : α -> G) : ∫ x : s, f x = ∫ x in s, f x
参数：hs : MeasurableSet s；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_subtype_comap`：integral_subtype_comap {α} [Measur
ableSpace α] {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (f : α -> G) : ∫
 x : s, f (x : α) ∂(Measur…
-/
theorem integral_subtype {α} [MeasureSpace α] {s : Set α} (hs : MeasurableSet s) (f : α → G) :
    ∫ x : s, f x = ∫ x in s, f x := integral_subtype_comap hs f

@[simp]
/-
**MeasureTheory.integral_dirac'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_dirac' [MeasurableSpace α] (f : α -> E) (a : α) (hfm : StronglyMe
asurable f) : ∫ x, f x ∂Measure.dirac a = f a
参数：f : α -> E；a : α；hfm : StronglyMeasurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_eq_dirac'`：ae_eq_dirac' [MeasurableSingletonClass β] {a
 : α} {f : α -> β} (hf : Measurable f) : f =ᵐ[dirac a] const α (f a)
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_dirac' [MeasurableSpace α] (f : α → E) (a : α) (hfm : StronglyMeasurable f) :
    ∫ x, f x ∂Measure.dirac a = f a := by
  borelize E
  calc
    ∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a :=
      integral_congr_ae <| ae_eq_dirac' hfm.measurable
    _ = f a := by simp

@[simp]
/-
**MeasureTheory.integral_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α -> 
E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
参数：f : α -> E；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_eq_dirac`：ae_eq_dirac [MeasurableSingletonClass α] {a :
 α} (f : α -> δ) : f =ᵐ[dirac a] const α (f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → E) (a : α) :
    ∫ x, f x ∂Measure.dirac a = f a :=
  calc
    ∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a := integral_congr_ae <| ae_eq_dirac f
    _ = f a := by simp
/-
**MeasureTheory.setIntegral_dirac'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_dirac' {mα : MeasurableSpace α} {f : α -> E} (hf : StronglyMea
surable f) (a : α) {s : Set α} (hs : MeasurableSet s) [Decidable (a in s)] : ∫ x
 in s, f x ∂Measure.dirac a = if a in s then f a else 0
参数：hf : StronglyMeasurable f；a : α；hs : MeasurableSet s；a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.restrict_dirac'`：restrict_dirac' (hs : MeasurableSet s) [D
ecidable (a in s)] : (Measure.dirac a).restrict s = if a in s then Measure.dirac
 a else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.integral_dirac'`：integral_dirac' [MeasurableSpace α] (f : 
α -> E) (a : α) (hfm : StronglyMeasurable f) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
-/
theorem setIntegral_dirac' {mα : MeasurableSpace α} {f : α → E} (hf : StronglyMeasurable f) (a : α)
    {s : Set α} (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac' hs]
  split_ifs
  · exact integral_dirac' _ _ hf
  · exact integral_zero_measure _
/-
**MeasureTheory.setIntegral_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α 
-> E) (a : α) (s : Set α) [Decidable (a in s)] : ∫ x in s, f x ∂Measure.dirac a 
= if a in s then f a else 0
参数：f : α -> E；a : α；s : Set α；a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.restrict_dirac`：restrict_dirac [MeasurableSingletonClass α
] [Decidable (a in s)] : (Measure.dirac a).restrict s = if a in s then Measure.d
irac a else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
-/
theorem setIntegral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → E) (a : α)
    (s : Set α) [Decidable (a ∈ s)] :
    ∫ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac]
  split_ifs
  · exact integral_dirac _ _
  · exact integral_zero_measure _

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
/-
**MeasureTheory.mul_meas_ge_le_integral_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：mul_meas_ge_le_integral_of_nonneg {f : α -> Real} (hf_nonneg : 0 <=ᵐ[μ] f)
 (hf_int : Integrable f μ) (ε : Real) : ε * μ.real { x | ε <= f x } <= ∫ x, f x 
∂μ
参数：hf_nonneg : 0 <=ᵐ[μ] f；hf_int : Integrable f μ；ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `MeasureTheory.ae_restrict_mem₀`：ae_restrict_mem₀ (hs : NullMeasurableSet
 s μ) : forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `AEMeasurable.nullMeasurable`：∀ {α : Type u_1} {β : Type u_2} {m0 : Measu
rableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}   {f : α → 
β}, AEMeasurable …
· 使用定理 `MeasureTheory.Integrable.aemeasurable`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]
   [inst_1 : ContinuousENor…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `MeasureTheory.integral_mono_measure`：integral_mono_measure [OrderClosedT
opology E] {f : α -> E} {ν : Measure α} (hle : μ <= ν) (hf : 0 <=ᵐ[ν] f) (hfi : 
Integrable f ν) : ∫ (a : …

--- 原说明 ---
**Markov's inequality** also known as **Chebyshev's first inequality**.
-/
theorem mul_meas_ge_le_integral_of_nonneg {f : α → ℝ} (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hf_int : Integrable f μ) (ε : ℝ) : ε * μ.real { x | ε ≤ f x } ≤ ∫ x, f x ∂μ := by
  rcases eq_top_or_lt_top (μ {x | ε ≤ f x}) with hμ | hμ
  · simpa [measureReal_def, hμ] using integral_nonneg_of_ae hf_nonneg
  · have := Fact.mk hμ
    calc
      ε * μ.real { x | ε ≤ f x } = ∫ _ in {x | ε ≤ f x}, ε ∂μ := by simp [mul_comm]
      _ ≤ ∫ x in {x | ε ≤ f x}, f x ∂μ :=
        integral_mono_ae (integrable_const _) (hf_int.mono_measure μ.restrict_le_self) <|
          ae_restrict_mem₀ <| hf_int.aemeasurable.nullMeasurable measurableSet_Ici
      _ ≤ _ := integral_mono_measure μ.restrict_le_self hf_nonneg hf_int

/-- Hölder's inequality for the integral of a product of norms. The integral of the product of two
norms of functions is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are
conjugate exponents. -/
/-
**MeasureTheory.integral_mul_norm_le_Lp_mul_Lq** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：integral_mul_norm_le_Lp_mul_Lq {E} [NormedAddCommGroup E] {f g : α -> E} {
p q : Real} (hpq : p.HolderConjugate q) (hf : MemLp f (ENNReal.ofReal p) μ) (hg 
: MemLp g (ENNReal.ofReal q) μ) : ∫ a, ‖f a‖ * ‖g a‖ ∂μ <= (∫ a, ‖f a‖ ^ p ∂μ) ^
 (1 / p) * (∫ a, ‖g a‖ ^ q ∂μ) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf : MemLp f (ENNReal.ofReal p) μ；hg : MemLp g (ENN
Real.ofReal q) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.pow`：AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasu
rable g μ) : AEMeasurable (fun x => f x ^ g x) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
Hölder's inequality for the integral of a product of norms. The integral of the 
product of two
norms of functions is bounded by the product of their `ℒp` and `ℒq` seminorms wh
en `p` and `q` are
conjugate exponents.
-/
theorem integral_mul_norm_le_Lp_mul_Lq {E} [NormedAddCommGroup E] {f g : α → E} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ a, ‖f a‖ * ‖g a‖ ∂μ ≤ (∫ a, ‖f a‖ ^ p ∂μ) ^ (1 / p) * (∫ a, ‖g a‖ ^ q ∂μ) ^ (1 / q) := by
  -- translate the Bochner integrals into Lebesgue integrals.
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae,
    integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Eventually.of_forall fun x ↦ by positivity
  · exact (hg.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by positivity
  · exact (hf.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by positivity
  · exact hf.1.norm.mul hg.1.norm
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  -- replace norms by nnnorm
  have h_left : ∫⁻ a, ENNReal.ofReal (‖f a‖ * ‖g a‖) ∂μ =
      ∫⁻ a, ((‖f ·‖ₑ) * (‖g ·‖ₑ)) a ∂μ := by
    simp_rw [Pi.mul_apply, ← ofReal_norm, ENNReal.ofReal_mul (norm_nonneg _)]
  have h_right_f : ∫⁻ a, .ofReal (‖f a‖ ^ p) ∂μ = ∫⁻ a, ‖f a‖ₑ ^ p ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.nonneg]
  have h_right_g : ∫⁻ a, .ofReal (‖g a‖ ^ q) ∂μ = ∫⁻ a, ‖g a‖ₑ ^ q ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.symm.nonneg]
  rw [h_left, h_right_f, h_right_g]
  -- we can now apply `ENNReal.lintegral_mul_le_Lp_mul_Lq` (up to the `toReal` application)
  refine ENNReal.toReal_mono ?_ ?_
  · refine ENNReal.mul_ne_top ?_ ?_
    · convert! hf.eLpNorm_ne_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
      · rw [ENNReal.toReal_ofReal hpq.nonneg]
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hpq.pos
      · finiteness
    · convert! hg.eLpNorm_ne_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
      · rw [ENNReal.toReal_ofReal hpq.symm.nonneg]
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hpq.symm.pos
      · finiteness
  · exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.1.nnnorm.aemeasurable.coe_nnreal_ennreal
      hg.1.nnnorm.aemeasurable.coe_nnreal_ennreal

/-- Hölder's inequality for functions `α → ℝ`. The integral of the product of two nonnegative
functions is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
/-
**MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：integral_mul_le_Lp_mul_Lq_of_nonneg {p q : Real} (hpq : p.HolderConjugate 
q) {f g : α -> Real} (hf_nonneg : 0 <=ᵐ[μ] f) (hg_nonneg : 0 <=ᵐ[μ] g) (hf : Mem
Lp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) μ) : ∫ a, f a * g a 
∂μ <= (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf_nonneg : 0 <=ᵐ[μ] f；hg_nonneg : 0 <=ᵐ[μ] g；hf : 
MemLp f (ENNReal.ofReal p) μ；hg : MemLp g (ENNReal.ofReal q) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq`：integral_mul_norm_le_Lp_mu
l_Lq {E} [NormedAddCommGroup E] {f g : α -> E} {p q : Real} (hpq : p.HolderConju
gate q) (hf : MemLp f (ENNReal.ofR…

--- 原说明 ---
Hölder's inequality for functions `α → ℝ`. The integral of the product of two no
nnegative
functions is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` an
d `q` are conjugate
exponents.
-/
theorem integral_mul_le_Lp_mul_Lq_of_nonneg {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q) := by
  have h_left : ∫ a, f a * g a ∂μ = ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg, hg_nonneg] with x hxf hxg
    rw [Real.norm_of_nonneg hxf, Real.norm_of_nonneg hxg]
  have h_right_f : ∫ a, f a ^ p ∂μ = ∫ a, ‖f a‖ ^ p ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg] with x hxf
    rw [Real.norm_of_nonneg hxf]
  have h_right_g : ∫ a, g a ^ q ∂μ = ∫ a, ‖g a‖ ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hg_nonneg] with x hxg
    rw [Real.norm_of_nonneg hxg]
  rw [h_left, h_right_f, h_right_g]
  exact integral_mul_norm_le_Lp_mul_Lq hpq hf hg
/-
**MeasureTheory.integral_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_singleton' {μ : Measure α} {f : α -> E} (hf : StronglyMeasurable 
f) (a : α) : ∫ a in {a}, f a ∂μ = μ.real {a} • f a
参数：hf : StronglyMeasurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_dirac'`：integral_dirac' [MeasurableSpace α] (f : 
α -> E) (a : α) (hfm : StronglyMeasurable f) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_singleton' {μ : Measure α} {f : α → E} (hf : StronglyMeasurable f) (a : α) :
    ∫ a in {a}, f a ∂μ = μ.real {a} • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac' f a hf,
    measureReal_def]
/-
**MeasureTheory.integral_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_singleton [MeasurableSingletonClass α] {μ : Measure α} (f : α -> 
E) (a : α) : ∫ a in {a}, f a ∂μ = μ.real {a} • f a
参数：f : α -> E；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_singleton [MeasurableSingletonClass α] {μ : Measure α} (f : α → E) (a : α) :
    ∫ a in {a}, f a ∂μ = μ.real {a} • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac, measureReal_def]
/-
**MeasureTheory.integral_unique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_unique [Unique α] (f : α -> E) : ∫ x, f x ∂μ = μ.real univ • f de
fault
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
-/
theorem integral_unique [Unique α] (f : α → E) : ∫ x, f x ∂μ = μ.real univ • f default :=
  calc
    ∫ x, f x ∂μ = ∫ _, f default ∂μ := by congr with x; congr; exact Unique.uniq _ x
    _ = μ.real univ • f default := by rw [integral_const]
/-
**MeasureTheory.integral_pos_of_integrable_nonneg_nonzero** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：integral_pos_of_integrable_nonneg_nonzero [TopologicalSpace α] [Measure.Is
OpenPosMeasure μ] {f : α -> Real} {x : α} (f_cont : Continuous f) (f_int : Integ
rable f μ) (f_nonneg : 0 <= f) (f_x : f x != 0) : 0 < ∫ x, f x ∂μ
参数：f_cont : Continuous f；f_int : Integrable f μ；f_nonneg : 0 <= f；f_x : f x != 0
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integral_pos_iff_support_of_nonneg`：integral_pos_iff_suppo
rt_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ) : (0 < ∫ x, f 
x ∂μ) ↔ 0 < μ (Function.support f)
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `Continuous.isOpen_support`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [T1Space X] [inst_2 : Zero X] [inst_3 : TopologicalSpace Y]   {f 
: Y → X}, Conti…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem integral_pos_of_integrable_nonneg_nonzero [TopologicalSpace α] [Measure.IsOpenPosMeasure μ]
    {f : α → ℝ} {x : α} (f_cont : Continuous f) (f_int : Integrable f μ) (f_nonneg : 0 ≤ f)
    (f_x : f x ≠ 0) : 0 < ∫ x, f x ∂μ :=
  (integral_pos_iff_support_of_nonneg f_nonneg f_int).2
    (IsOpen.measure_pos μ f_cont.isOpen_support ⟨x, f_x⟩)

end Properties

section IntegralTrim

variable {β γ : Type*} {m m0 : MeasurableSpace β} {μ : Measure β}

/-- Simple function seen as simple function of a larger `MeasurableSpace`. -/
/-
**MeasureTheory.SimpleFunc.toLargerSpace** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：{β : Type u_6} →   {γ : Type u_7} → {m m0 : MeasurableSpace β} → m ≤ m0 → 
MeasureTheory.SimpleFunc β γ → MeasureTheory.SimpleFunc β γ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.finite_range`：finite_range (f : α ->ₛ β) : (Set
.range f).Finite

--- 原说明 ---
Simple function seen as simple function of a larger `MeasurableSpace`.
-/
def SimpleFunc.toLargerSpace (hm : m ≤ m0) (f : @SimpleFunc β m γ) : SimpleFunc β γ :=
  ⟨@SimpleFunc.toFun β m γ f, fun x => hm _ (@SimpleFunc.measurableSet_fiber β γ m f x),
    @SimpleFunc.finite_range β γ m f⟩
/-
**MeasureTheory.SimpleFunc.coe_toLargerSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：∀ {β : Type u_6} {γ : Type u_7} {m m0 : MeasurableSpace β} (hm : m ≤ m0) (
f : MeasureTheory.SimpleFunc β γ),   ⇑(MeasureTheory.SimpleFunc.toLargerSpace hm
 f) = ⇑f
参数：hm : m ≤ m0；f : MeasureTheory.SimpleFunc β γ；MeasureTheory.SimpleFunc.toLarge
rSpace hm f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SimpleFunc.coe_toLargerSpace_eq (hm : m ≤ m0) (f : @SimpleFunc β m γ) :
    ⇑(f.toLargerSpace hm) = f := rfl
/-
**MeasureTheory.integral_simpleFunc_larger_space** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integral_simpleFunc_larger_space (hm : m <= m0) (f : @SimpleFunc β m F) (h
f_int : Integrable f μ) : ∫ x, f x ∂μ = ∑ x in @SimpleFunc.range β F m f, μ.real
 (f ⁻¹' {x}) • x
参数：hm : m <= m0；f : @SimpleFunc β m F；hf_int : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq_sum`：∀ {α : Type u_1} {E : Type u_2
} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {m : MeasurableSpace 
α}   {μ : MeasureTheory.Measur…
-/
theorem integral_simpleFunc_larger_space (hm : m ≤ m0) (f : @SimpleFunc β m F)
    (hf_int : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x ∈ @SimpleFunc.range β F m f, μ.real (f ⁻¹' {x}) • x := by
  simp_rw [← f.coe_toLargerSpace_eq hm]
  rw [SimpleFunc.integral_eq_sum _ hf_int]
  congr 1
/-
**MeasureTheory.integral_trim_simpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_trim_simpleFunc (hm : m <= m0) (f : @SimpleFunc β m F) (hf_int : 
Integrable f μ) : ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm
参数：hm : m <= m0；f : @SimpleFunc β m F；hf_int : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
· 使用定理 `MeasureTheory.Integrable.trim`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{H : Type u_8} [inst : NormedAddCommGroup H] {m0 : MeasurableSpace α}   {μ' : Me
asureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_simpleFunc_larger_space`：integral_simpleFunc_larg
er_space (hm : m <= m0) (f : @SimpleFunc β m F) (hf_int : Integrable f μ) : ∫ x,
 f x ∂μ = ∑ x in @SimpleFunc.range β…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
-/
theorem integral_trim_simpleFunc (hm : m ≤ m0) (f : @SimpleFunc β m F) (hf_int : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  have hf : StronglyMeasurable[m] f := @SimpleFunc.stronglyMeasurable β F m _ f
  have hf_int_m := hf_int.trim hm hf
  rw [integral_simpleFunc_larger_space (le_refl m) f hf_int_m,
    integral_simpleFunc_larger_space hm f hf_int]
  congr with x
  simp only [measureReal_def]
  congr 2
  exact (trim_measurableSet_eq hm (@SimpleFunc.measurableSet_fiber β F m f x)).symm
/-
**MeasureTheory.integral_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_trim (hm : m <= m0) {f : β -> G} (hf : StronglyMeasurable[m] f) :
 ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm
参数：hm : m <= m0；hf : StronglyMeasurable[m] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
· 使用定理 `MeasureTheory.SimpleFunc.integrable_approxOn_range`：integrable_approxOn_
range [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) [Separa
bleSpace (range f union {0} : Set E)] (h…
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Integrable.trim`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{H : Type u_8} [inst : NormedAddCommGroup H] {m0 : MeasurableSpace α}   {μ' : Me
asureTheory.Measure…
· 使用定理 `MeasureTheory.integral_trim_simpleFunc`：integral_trim_simpleFunc (hm : m
 <= m0) (f : @SimpleFunc β m F) (hf_int : Integrable f μ) : ∫ x, f x ∂μ = ∫ x, f
 x ∂μ.trim hm
· 使用定理 `MeasureTheory.tendsto_integral_of_L1`：tendsto_integral_of_L1 {ι} (f : α 
-> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G} {l : Filter ι} (hFi : f
orallᶠ i in l, Integrable …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn_range_L1_enorm`：tendsto_approx
On_range_L1_enorm [OpensMeasurableSpace E] {f : β -> E} {μ : Measure β} [Separab
leSpace (range f union {0} : Set E)] (fmeas : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.integrable_of_integrable_trim`：integrable_of_integrable_tr
im (hm : m <= m0) (hf_int : Integrable f (μ'.trim hm)) : Integrable f μ'
（共 34 条，此处仅展示前 30 条）
-/
theorem integral_trim (hm : m ≤ m0) {f : β → G} (hf : StronglyMeasurable[m] f) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  borelize G
  by_cases hf_int : Integrable f μ
  swap
  · have hf_int_m : ¬Integrable f (μ.trim hm) := fun hf_int_m =>
      hf_int (integrable_of_integrable_trim hm hf_int_m)
    rw [integral_undef hf_int, integral_undef hf_int_m]
  have : SeparableSpace (range f ∪ {0} : Set G) := hf.separableSpace_range_union_singleton
  let f_seq := @SimpleFunc.approxOn G β _ _ _ m _ hf.measurable (range f ∪ {0}) 0 (by simp) _
  have hf_seq_meas : ∀ n, StronglyMeasurable[m] (f_seq n) := fun n =>
    @SimpleFunc.stronglyMeasurable β G m _ (f_seq n)
  have hf_seq_int : ∀ n, Integrable (f_seq n) μ :=
    SimpleFunc.integrable_approxOn_range (hf.mono hm).measurable hf_int
  have hf_seq_int_m : ∀ n, Integrable (f_seq n) (μ.trim hm) := fun n =>
    (hf_seq_int n).trim hm (hf_seq_meas n)
  have hf_seq_eq : ∀ n, ∫ x, f_seq n x ∂μ = ∫ x, f_seq n x ∂μ.trim hm := fun n =>
    integral_trim_simpleFunc hm (f_seq n) (hf_seq_int n)
  have h_lim_1 : atTop.Tendsto (fun n => ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_integral_of_L1 f hf_int.1 (Eventually.of_forall hf_seq_int) ?_
    exact SimpleFunc.tendsto_approxOn_range_L1_enorm (hf.mono hm).measurable hf_int
  have h_lim_2 : atTop.Tendsto (fun n => ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂μ.trim hm)) := by
    simp_rw [hf_seq_eq]
    refine @tendsto_integral_of_L1 β G _ _ m (μ.trim hm) _ f (hf_int.trim hm hf).1 _ _
      (Eventually.of_forall hf_seq_int_m) ?_
    exact @SimpleFunc.tendsto_approxOn_range_L1_enorm β G m _ _ _ f _ _ hf.measurable
      (hf_int.trim hm hf)
  exact tendsto_nhds_unique h_lim_1 h_lim_2
/-
**MeasureTheory.integral_trim_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_trim_ae (hm : m <= m0) {f : β -> G} (hf : AEStronglyMeasurable[m]
 f (μ.trim hm)) : ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm
参数：hm : m <= m0；hf : AEStronglyMeasurable[m] f (μ.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.integral_trim`：integral_trim (hm : m <= m0) {f : β -> G} (
hf : StronglyMeasurable[m] f) : ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
-/
theorem integral_trim_ae (hm : m ≤ m0) {f : β → G} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  rw [integral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), integral_congr_ae hf.ae_eq_mk]
  exact integral_trim hm hf.stronglyMeasurable_mk

end IntegralTrim

section SnormBound

variable {m0 : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

/-
**MeasureTheory.eLpNorm_one_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_one_le_of_le {r : Real>=0} (hfint : Integrable f μ) (hfint' : 0 <=
 ∫ x, f x ∂μ) (hf : forallᵐ ω ∂μ, f ω <= r) : eLpNorm f 1 μ <= 2 * μ Set.univ * 
r
参数：hfint : Integrable f μ；hfint' : 0 <= ∫ x, f x ∂μ；hf : forallᵐ ω ∂μ, f ω <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `MeasureTheory.integral_nonpos_of_ae`：integral_nonpos_of_ae {f : α -> E} 
(hf : f <=ᵐ[μ] 0) : ∫ x, f x ∂μ <= 0
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integral_eq_zero_iff_of_nonneg_ae`：integral_eq_zero_iff_of
_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) : ∫ x, f x ∂
μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用定理 `Right.nonneg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddRightMono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
（共 77 条，此处仅展示前 30 条）
-/
theorem eLpNorm_one_le_of_le {r : ℝ≥0} (hfint : Integrable f μ) (hfint' : 0 ≤ ∫ x, f x ∂μ)
    (hf : ∀ᵐ ω ∂μ, f ω ≤ r) : eLpNorm f 1 μ ≤ 2 * μ Set.univ * r := by
  by_cases hr : r = 0
  · suffices f =ᵐ[μ] 0 by
      rw [eLpNorm_congr_ae this, eLpNorm_zero, hr, ENNReal.coe_zero, mul_zero]
    rw [hr] at hf
    norm_cast at hf
    have hnegf : ∫ x, -f x ∂μ = 0 := by
      rw [integral_neg, neg_eq_zero]
      exact le_antisymm (integral_nonpos_of_ae hf) hfint'
    have := (integral_eq_zero_iff_of_nonneg_ae ?_ hfint.neg).1 hnegf
    · filter_upwards [this] with ω hω
      rwa [Pi.neg_apply, Pi.zero_apply, neg_eq_zero] at hω
    · filter_upwards [hf] with ω hω
      rwa [Pi.zero_apply, Pi.neg_apply, Right.nonneg_neg_iff]
  by_cases hμ : IsFiniteMeasure μ
  swap
  · have : μ Set.univ = ∞ := by
      by_contra hμ'
      exact hμ (IsFiniteMeasure.mk <| lt_top_iff_ne_top.2 hμ')
    rw [this, ENNReal.mul_top', if_neg, ENNReal.top_mul', if_neg]
    · exact le_top
    · simp [hr]
    · simp
  have := hμ
  rw [integral_eq_integral_pos_part_sub_integral_neg_part hfint, sub_nonneg] at hfint'
  have hposbdd : ∫ ω, max (f ω) 0 ∂μ ≤ μ.real Set.univ • (r : ℝ) := by
    rw [← integral_const]
    refine integral_mono_ae hfint.real_toNNReal (integrable_const (r : ℝ)) ?_
    filter_upwards [hf] with ω hω using Real.toNNReal_le_iff_le_coe.2 hω
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
      (memLp_one_iff_integrable.2 hfint),
    ENNReal.ofReal_le_iff_le_toReal (by finiteness)]
  simp_rw [ENNReal.toReal_one, _root_.inv_one, Real.rpow_one, Real.norm_eq_abs, ←
    max_zero_add_max_neg_zero_eq_abs_self, ← Real.coe_toNNReal']
  rw [integral_add hfint.real_toNNReal]
  · simp only [Real.coe_toNNReal', ENNReal.toReal_mul, ENNReal.coe_toReal,
      toReal_ofNat] at hfint' ⊢
    grw [hfint']
    rwa [← two_mul, mul_assoc, mul_le_mul_iff_right₀ (two_pos : (0 : ℝ) < 2)]
  · exact hfint.neg.sup (integrable_zero _ _ μ)
/-
**MeasureTheory.eLpNorm_one_le_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_one_le_of_le' {r : Real} (hfint : Integrable f μ) (hfint' : 0 <= ∫
 x, f x ∂μ) (hf : forallᵐ ω ∂μ, f ω <= r) : eLpNorm f 1 μ <= 2 * μ Set.univ * EN
NReal.ofReal r
参数：hfint : Integrable f μ；hfint' : 0 <= ∫ x, f x ∂μ；hf : forallᵐ ω ∂μ, f ω <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_one_le_of_le`：eLpNorm_one_le_of_le {r : Real>=0} (
hfint : Integrable f μ) (hfint' : 0 <= ∫ x, f x ∂μ) (hf : forallᵐ ω ∂μ, f ω <= r
) : eLpNorm f 1 μ <= 2 *…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem eLpNorm_one_le_of_le' {r : ℝ} (hfint : Integrable f μ) (hfint' : 0 ≤ ∫ x, f x ∂μ)
    (hf : ∀ᵐ ω ∂μ, f ω ≤ r) : eLpNorm f 1 μ ≤ 2 * μ Set.univ * ENNReal.ofReal r := by
  refine eLpNorm_one_le_of_le hfint hfint' ?_
  simp only [Real.coe_toNNReal', le_max_iff]
  filter_upwards [hf] with ω hω using Or.inl hω

end SnormBound

end MeasureTheory

namespace Mathlib.Meta.Positivity

open Qq Lean Meta MeasureTheory

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for integrals.

This extension only proves non-negativity, strict positivity is more delicate for integration and
requires more assumptions. -/
@[positivity MeasureTheory.integral _ _]
meta def evalIntegral : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@MeasureTheory.integral $i ℝ _ $inst2 _ _ $f) =>
    let i : Q($i) ← mkFreshExprMVarQ q($i) .syntheticOpaque
    have body : Q(ℝ) := .betaRev f #[i]
    let rbody ← core zα pα body
    let pbody ← rbody.toNonneg
    let pr : Q(∀ x, 0 ≤ $f x) ← mkLambdaFVars #[i] pbody
    assertInstancesCommute
    return .nonnegative q(integral_nonneg $pr)
  | _ => throwError "not MeasureTheory.integral"

end Mathlib.Meta.Positivity

