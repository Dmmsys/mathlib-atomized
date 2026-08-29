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

  * `integral_zero` : `∫ 0 ∂μ = 0`
  * `integral_add` : `∫ x, f x + g x ∂μ = ∫ x, f ∂μ + ∫ x, g x ∂μ`
  * `integral_neg` : `∫ x, - f x ∂μ = - ∫ x, f x ∂μ`
  * `integral_sub` : `∫ x, f x - g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ`
  * `integral_smul` : `∫ x, r • f x ∂μ = r • ∫ x, f x ∂μ`
  * `integral_congr_ae` : `f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ`
  * `norm_integral_le_integral_norm` : `‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ`

2. Basic order properties of the Bochner integral on functions of type `α → E`, where `α` is a
   measure space and `E` is a real ordered Banach space.

  * `integral_nonneg_of_ae` : `0 ≤ᵐ[μ] f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos_of_ae` : `f ≤ᵐ[μ] 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono_ae` : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`
  * `integral_nonneg` : `0 ≤ f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos` : `f ≤ 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono` : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`

3. Propositions connecting the Bochner integral with the integral on `ℝ≥0∞`-valued functions,
   which is called `lintegral` and has the notation `∫⁻`.

  * `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` :
    `∫ x, f x ∂μ = ∫⁻ x, f⁺ x ∂μ - ∫⁻ x, f⁻ x ∂μ`,
    where `f⁺` is the positive part of `f` and `f⁻` is the negative part of `f`.
  * `integral_eq_lintegral_of_nonneg_ae` : `0 ≤ᵐ[μ] f → ∫ x, f x ∂μ = ∫⁻ x, f x ∂μ`

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

local infixr:25 " ->ₛ " => SimpleFunc

/-!
## The Bochner integral on functions

Define the Bochner integral on functions generally to be the `L1` Bochner integral, for integrable
functions, and 0 otherwise; prove its basic properties.
-/

variable [NormedAddCommGroup E] [NormedDivisionRing 𝕜]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]

open scoped Classical in
/-- The Bochner integral -/
irreducible_def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α -> G) : G :=
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

variable [NormedSpace Real E]
variable {f : α -> E} {m : MeasurableSpace α} {μ : Measure α}

section Basic

/--
theorem `integral_eq` / 定理 `integral_eq`

English:
theorem integral_eq
  given: [hE : CompleteSpace E] (f : α -> E) (hf : Integrable f μ)
  proof: by
  simp [integral, hE, hf]

中文:
定理 integral_eq
  条件: [hE : 完备空间 E] (f : α -> E) (hf : 可积 f μ)
  证明: by
  simp [integral, hE, hf]

Depends on / 依赖: integral
-/
theorem integral_eq [hE : CompleteSpace E] (f : α -> E) (hf : Integrable f μ) :
    ∫ a, f a ∂μ = L1.integral (hf.toL1 f) := by
  simp [integral, hE, hf]

/--
theorem `integral_eq_setToFun` / 定理 `integral_eq_setToFun`

English:
theorem integral_eq_setToFun
  given: (f : α -> E)
  proof: by
  by_cases hE : CompleteSpace E
  · simp only [integral, hE, ↓reduceDIte, L1.integral, setToFun]
    rfl
  · simp [integral, hE, setToFun]

中文:
定理 integral_eq_setToFun
  条件: (f : α -> E)
  证明: by
  by_cases hE : CompleteSpace E
  · simp only [integral, hE, ↓reduceDIte, L1.integral, setToFun]
    rfl
  · simp [integral, hE, setToFun]

Depends on / 依赖: CompleteSpace, L1.integral, integral, reduceDIte, setToFun
-/
theorem integral_eq_setToFun (f : α -> E) :
    ∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul μ) f := by
  by_cases hE : CompleteSpace E
  · simp only [integral, hE, ↓reduceDIte, L1.integral, setToFun]
    rfl
  · simp [integral, hE, setToFun]

/--
theorem `L1.integral_eq_integral` / 定理 `L1.integral_eq_integral`

English:
theorem L1.integral_eq_integral
  given: [CompleteSpace E] (f : α ->₁[μ] E)
  proof: by
  simp only [integral, L1.integral, integral_eq_setToFun]
  exact (L1.setToFun_eq_setToL1 (dominatedFinMeasAdditive_weightedSMul μ) f).symm

中文:
定理 L1.integral_eq_integral
  条件: [完备空间 E] (f : α ->₁[μ] E)
  证明: by
  simp only [integral, L1.integral, integral_eq_setToFun]
  exact (L1.setToFun_eq_setToL1 (dominatedFinMeasAdditive_weightedSMul μ) f).symm

Depends on / 依赖: L1.integral, L1.setToFun_eq_setToL1, dominatedFinMeasAdditive_weightedSMul, integral, integral_eq_setToFun, setToFun_eq_setToL1
-/
theorem L1.integral_eq_integral [CompleteSpace E] (f : α ->₁[μ] E) :
    L1.integral f = ∫ a, f a ∂μ := by
  simp only [integral, L1.integral, integral_eq_setToFun]
  exact (L1.setToFun_eq_setToL1 (dominatedFinMeasAdditive_weightedSMul μ) f).symm

/--
theorem `integral_undef` / 定理 `integral_undef`

English:
theorem integral_undef
  given: {f : α -> G} (h : ¬Integrable f μ)
  statement: ∫ a, f a ∂μ = 0
  proof: by
  simp only [integral_eq_setToFun]
  exact setToFun_undef (dominatedFinMeasAdditive_weightedSMul μ) h

中文:
定理 integral_undef
  条件: {f : α -> G} (h : ¬可积 f μ)
  结论: ∫ a, f a ∂μ = 0
  证明: by
  simp only [integral_eq_setToFun]
  exact setToFun_undef (dominatedFinMeasAdditive_weightedSMul μ) h

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_undef
-/
theorem integral_undef {f : α -> G} (h : ¬Integrable f μ) : ∫ a, f a ∂μ = 0 := by
  simp only [integral_eq_setToFun]
  exact setToFun_undef (dominatedFinMeasAdditive_weightedSMul μ) h

/--
theorem `Integrable.of_integral_ne_zero` / 定理 `Integrable.of_integral_ne_zero`

English:
theorem Integrable.of_integral_ne_zero
  given: {f : α -> G} (h : ∫ a, f a ∂μ != 0)
  statement: Integrable f μ
  proof: Not.imp_symm integral_undef h

中文:
定理 可积.of_integral_ne_zero
  条件: {f : α -> G} (h : ∫ a, f a ∂μ != 0)
  结论: 可积 f μ
  证明: Not.imp_symm integral_undef h

Depends on / 依赖: Not.imp_symm, imp_symm, integral_undef
-/
theorem Integrable.of_integral_ne_zero {f : α -> G} (h : ∫ a, f a ∂μ != 0) : Integrable f μ :=
  Not.imp_symm integral_undef h

/--
theorem `integral_non_aestronglyMeasurable` / 定理 `integral_non_aestronglyMeasurable`

English:
theorem integral_non_aestronglyMeasurable
  given: {f : α -> G} (h : ¬AEStronglyMeasurable f μ)
  proof: integral_undef not_and_of_not_left _ h

中文:
定理 integral_non_aestronglyMeasurable
  条件: {f : α -> G} (h : ¬AEStronglyMeasurable f μ)
  证明: integral_undef not_and_of_not_left _ h

Depends on / 依赖: integral_undef, not_and_of_not_left
-/
theorem integral_non_aestronglyMeasurable {f : α -> G} (h : ¬AEStronglyMeasurable f μ) :
    ∫ a, f a ∂μ = 0 :=
integral_undef not_and_of_not_left _ h

/--
theorem `integral_of_not_completeSpace` / 定理 `integral_of_not_completeSpace`

English:
theorem integral_of_not_completeSpace
  given: {f : α -> G} (hG : ¬CompleteSpace G)
  proof: by
  simp [integral, hG]

中文:
定理 integral_of_not_completeSpace
  条件: {f : α -> G} (hG : ¬完备空间 G)
  证明: by
  simp [integral, hG]

Depends on / 依赖: integral
-/
theorem integral_of_not_completeSpace {f : α -> G} (hG : ¬CompleteSpace G) :
    ∫ a, f a ∂μ = 0 := by
  simp [integral, hG]

variable (α G)

@[simp]
/--
theorem `integral_zero` / 定理 `integral_zero`

English:
theorem integral_zero
  statement: ∫ _ : α, (0 : G) ∂μ = 0
  proof: by
  simp only [integral_eq_setToFun]
  apply setToFun_zero

@[simp]

中文:
定理 integral_zero
  结论: ∫ _ : α, (0 : G) ∂μ = 0
  证明: by
  simp only [integral_eq_setToFun]
  apply setToFun_zero

@[simp]

Depends on / 依赖: integral_eq_setToFun, setToFun_zero
-/
theorem integral_zero : ∫ _ : α, (0 : G) ∂μ = 0 := by
  simp only [integral_eq_setToFun]
  apply setToFun_zero

@[simp]
/--
theorem `integral_zero'` / 定理 `integral_zero'`

English:
theorem integral_zero'
  statement: integral μ (0 : α -> G) = 0
  proof: integral_zero α G

中文:
定理 integral_zero'
  结论: integral μ (0 : α -> G) = 0
  证明: integral_zero α G

Depends on / 依赖: integral_zero
-/
theorem integral_zero' : integral μ (0 : α -> G) = 0 :=
  integral_zero α G

/--
lemma `integral_indicator₂` / 引理 `integral_indicator₂`

English:
lemma integral_indicator₂
  given: {β : Type*} (f : β -> α -> G) (s : Set β) (b : β)
  proof: by
  by_cases hb : b in s <;> simp [hb]

中文:
引理 integral_indicator₂
  条件: {β : 类型} (f : β -> α -> G) (s : 集合 β) (b : β)
  证明: by
  by_cases hb : b in s <;> simp [hb]
-/
lemma integral_indicator₂ {β : Type*} (f : β -> α -> G) (s : Set β) (b : β) :
    ∫ y, s.indicator (f · y) b ∂μ = s.indicator (fun x => ∫ y, f x y ∂μ) b := by
  by_cases hb : b in s <;> simp [hb]

variable {α G}

/--
theorem `integrable_of_integral_eq_one` / 定理 `integrable_of_integral_eq_one`

English:
theorem integrable_of_integral_eq_one
  given: {f : α -> Real} (h : ∫ x, f x ∂μ = 1)
  statement: Integrable f μ
  proof: .of_integral_ne_zero h ▸ one_ne_zero

中文:
定理 integrable_of_integral_eq_one
  条件: {f : α -> 实数} (h : ∫ x, f x ∂μ = 1)
  结论: 可积 f μ
  证明: .of_integral_ne_zero h ▸ one_ne_zero

Depends on / 依赖: of_integral_ne_zero, one_ne_zero
-/
theorem integrable_of_integral_eq_one {f : α -> Real} (h : ∫ x, f x ∂μ = 1) : Integrable f μ :=
.of_integral_ne_zero h ▸ one_ne_zero

/--
theorem `integral_add` / 定理 `integral_add`

English:
theorem integral_add
  given: {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: by
  simp only [integral_eq_setToFun]
  exact setToFun_add (dominatedFinMeasAdditive_weightedSMul μ) hf hg

中文:
定理 integral_add
  条件: {f g : α -> G} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: by
  simp only [integral_eq_setToFun]
  exact setToFun_add (dominatedFinMeasAdditive_weightedSMul μ) hf hg

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_add
-/
theorem integral_add {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_add (dominatedFinMeasAdditive_weightedSMul μ) hf hg

/--
theorem `integral_add'` / 定理 `integral_add'`

English:
theorem integral_add'
  given: {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: integral_add hf hg

中文:
定理 integral_add'
  条件: {f g : α -> G} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: integral_add hf hg

Depends on / 依赖: integral_add
-/
theorem integral_add' {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg

/--
theorem `integral_finsetSum` / 定理 `integral_finsetSum`

English:
theorem integral_finsetSum
  given: {ι} (s : Finset ι) {f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ)
  proof: by
  simp only [integral_eq_setToFun]
  exact setToFun_finsetSum (dominatedFinMeasAdditive_weightedSMul _) s hf

@[deprecated (since := "2026-04-08")] alias integral_finset_sum := integral_finsetSum

@[integral_simps]

中文:
定理 integral_finsetSum
  条件: {ι} (s : 有限集 ι) {f : ι -> α -> G} (hf : 对任意 i in s, 可积 (f i) μ)
  证明: by
  simp only [integral_eq_setToFun]
  exact setToFun_finsetSum (dominatedFinMeasAdditive_weightedSMul _) s hf

@[deprecated (since := "2026-04-08")] alias integral_finset_sum := integral_finsetSum

@[integral_simps]

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_finsetSum
-/
theorem integral_finsetSum {ι} (s : Finset ι) {f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) :
    ∫ a, ∑ i in s, f i a ∂μ = ∑ i in s, ∫ a, f i a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_finsetSum (dominatedFinMeasAdditive_weightedSMul _) s hf

@[deprecated (since := "2026-04-08")] alias integral_finset_sum := integral_finsetSum

@[integral_simps]
/--
theorem `integral_neg` / 定理 `integral_neg`

English:
theorem integral_neg
  given: (f : α -> G)
  statement: ∫ a, -f a ∂μ = -∫ a, f a ∂μ
  proof: by
  simp only [integral_eq_setToFun]
  exact setToFun_neg (dominatedFinMeasAdditive_weightedSMul μ) f

中文:
定理 integral_neg
  条件: (f : α -> G)
  结论: ∫ a, -f a ∂μ = -∫ a, f a ∂μ
  证明: by
  simp only [integral_eq_setToFun]
  exact setToFun_neg (dominatedFinMeasAdditive_weightedSMul μ) f

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_neg
-/
theorem integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -∫ a, f a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_neg (dominatedFinMeasAdditive_weightedSMul μ) f

/--
theorem `integral_neg'` / 定理 `integral_neg'`

English:
theorem integral_neg'
  given: (f : α -> G)
  statement: ∫ a, (-f) a ∂μ = -∫ a, f a ∂μ
  proof: integral_neg f

中文:
定理 integral_neg'
  条件: (f : α -> G)
  结论: ∫ a, (-f) a ∂μ = -∫ a, f a ∂μ
  证明: integral_neg f

Depends on / 依赖: integral_neg
-/
theorem integral_neg' (f : α -> G) : ∫ a, (-f) a ∂μ = -∫ a, f a ∂μ :=
  integral_neg f

/--
theorem `integral_sub` / 定理 `integral_sub`

English:
theorem integral_sub
  given: {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: by
  simp only [integral_eq_setToFun]
  exact setToFun_sub (dominatedFinMeasAdditive_weightedSMul μ) hf hg

中文:
定理 integral_sub
  条件: {f g : α -> G} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: by
  simp only [integral_eq_setToFun]
  exact setToFun_sub (dominatedFinMeasAdditive_weightedSMul μ) hf hg

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_sub
-/
theorem integral_sub {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_sub (dominatedFinMeasAdditive_weightedSMul μ) hf hg

/--
theorem `integral_sub'` / 定理 `integral_sub'`

English:
theorem integral_sub'
  given: {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: integral_sub hf hg

中文:
定理 integral_sub'
  条件: {f g : α -> G} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: integral_sub hf hg

Depends on / 依赖: integral_sub
-/
theorem integral_sub' {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
  integral_sub hf hg

/-- The Bochner integral is linear. Note this requires `𝕜` to be a normed division ring, in order
to ensure that for `c ≠ 0`, the function `c • f` is integrable iff `f` is. For an analogous
statement for more general rings with an *a priori* integrability assumption on `f`, see
`MeasureTheory.Integrable.integral_smul`. -/
@[integral_simps]
/--
theorem `integral_smul` / 定理 `integral_smul`

English:
theorem integral_smul
  given: [Module 𝕜 G] [NormSMulClass 𝕜 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G)
  proof: by
  simp only [integral_eq_setToFun]
  exact setToFun_smul (dominatedFinMeasAdditive_weightedSMul μ) weightedSMul_smul c f

中文:
定理 integral_smul
  条件: [模 𝕜 G] [NormSMul类 𝕜 G] [标量交换类 实数 𝕜 G] (c : 𝕜) (f : α -> G)
  证明: by
  simp only [integral_eq_setToFun]
  exact setToFun_smul (dominatedFinMeasAdditive_weightedSMul μ) weightedSMul_smul c f

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_smul, weightedSMul_smul
-/
theorem integral_smul [Module 𝕜 G] [NormSMulClass 𝕜 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) :
    ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_smul (dominatedFinMeasAdditive_weightedSMul μ) weightedSMul_smul c f

/--
theorem `Integrable.integral_smul` / 定理 `Integrable.integral_smul`

English:
theorem Integrable.integral_smul
  statement: {R : Type*} [NormedRing R] [Module R G] [IsBoundedSMul R G]
  proof: by
  by_cases hG : CompleteSpace G
  · simpa only [integral, hG, hf, hf.fun_smul c] using! L1.integral_smul c (toL1 f hf)
  · simp [integral, hG]

中文:
定理 可积.integral_smul
  结论: {R : 类型} [赋范环 R] [模 R G] [是BoundedSMul R G]
  证明: by
  by_cases hG : CompleteSpace G
  · simpa only [integral, hG, hf, hf.fun_smul c] using! L1.integral_smul c (toL1 f hf)
  · simp [integral, hG]

Depends on / 依赖: CompleteSpace, L1.integral_smul, fun_smul, hf.fun_smul, integral, integral_smul
-/
theorem Integrable.integral_smul {R : Type*} [NormedRing R] [Module R G] [IsBoundedSMul R G]
    [SMulCommClass Real R G] (c : R)
    {f : α -> G} (hf : Integrable f μ) :
    ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simpa only [integral, hG, hf, hf.fun_smul c] using! L1.integral_smul c (toL1 f hf)
  · simp [integral, hG]

/--
theorem `integral_const_mul` / 定理 `integral_const_mul`

English:
theorem integral_const_mul
  given: {L : Type*} [RCLike L] (r : L) (f : α -> L)
  proof: integral_smul r f

中文:
定理 integral_const_mul
  条件: {L : 类型} [RCLike L] (r : L) (f : α -> L)
  证明: integral_smul r f

Depends on / 依赖: integral_smul
-/
theorem integral_const_mul {L : Type*} [RCLike L] (r : L) (f : α -> L) :
    ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ :=
  integral_smul r f

/--
theorem `integral_mul_const` / 定理 `integral_mul_const`

English:
theorem integral_mul_const
  given: {L : Type*} [RCLike L] (r : L) (f : α -> L)
  proof: by simp only [mul_comm, integral_const_mul r f]

中文:
定理 integral_mul_const
  条件: {L : 类型} [RCLike L] (r : L) (f : α -> L)
  证明: by simp only [mul_comm, integral_const_mul r f]

Depends on / 依赖: integral_const_mul, mul_comm
-/
theorem integral_mul_const {L : Type*} [RCLike L] (r : L) (f : α -> L) :
    ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r := by simp only [mul_comm, integral_const_mul r f]

/--
theorem `integral_div` / 定理 `integral_div`

English:
theorem integral_div
  given: {L : Type*} [RCLike L] (r : L) (f : α -> L)
  proof: by
  simpa only [← div_eq_mul_inv] using integral_mul_const r⁻¹ f

中文:
定理 integral_div
  条件: {L : 类型} [RCLike L] (r : L) (f : α -> L)
  证明: by
  simpa only [← div_eq_mul_inv] using integral_mul_const r⁻¹ f

Depends on / 依赖: div_eq_mul_inv, integral_mul_const
-/
theorem integral_div {L : Type*} [RCLike L] (r : L) (f : α -> L) :
    ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r := by
  simpa only [← div_eq_mul_inv] using integral_mul_const r⁻¹ f

/--
theorem `integral_congr_ae` / 定理 `integral_congr_ae`

English:
theorem integral_congr_ae
  given: {f g : α -> G} (h : f =ᵐ[μ] g)
  statement: ∫ a, f a ∂μ = ∫ a, g a ∂μ
  proof: by
  simp only [integral_eq_setToFun]
  exact setToFun_congr_ae (dominatedFinMeasAdditive_weightedSMul μ) h

中文:
定理 integral_congr_ae
  条件: {f g : α -> G} (h : f =ᵐ[μ] g)
  结论: ∫ a, f a ∂μ = ∫ a, g a ∂μ
  证明: by
  simp only [integral_eq_setToFun]
  exact setToFun_congr_ae (dominatedFinMeasAdditive_weightedSMul μ) h

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_congr_ae
-/
theorem integral_congr_ae {f g : α -> G} (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_congr_ae (dominatedFinMeasAdditive_weightedSMul μ) h

/--
lemma `integral_congr_ae₂` / 引理 `integral_congr_ae₂`

English:
lemma integral_congr_ae₂
  statement: {β : Type*} {_ : MeasurableSpace β} {ν : Measure β} {f g : α -> β -> G}
  proof: by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

@[simp]

中文:
引理 integral_congr_ae₂
  结论: {β : 类型} {_ : 可测空间 β} {ν : 测度 β} {f g : α -> β -> G}
  证明: by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

@[simp]

Depends on / 依赖: filter_upwards, integral_congr_ae
-/
lemma integral_congr_ae₂ {β : Type*} {_ : MeasurableSpace β} {ν : Measure β} {f g : α -> β -> G}
    (h : forallᵐ a ∂μ, f a =ᵐ[ν] g a) :
    ∫ a, ∫ b, f a b ∂ν ∂μ = ∫ a, ∫ b, g a b ∂ν ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

@[simp]
/--
theorem `L1.integral_of_fun_eq_integral'` / 定理 `L1.integral_of_fun_eq_integral'`

English:
theorem L1.integral_of_fun_eq_integral'
  given: {f : α -> G} (hf : Integrable f μ)
  proof: by
  simp only [integral_eq_setToFun]
  exact setToFun_toL1 (dominatedFinMeasAdditive_weightedSMul μ) hf

中文:
定理 L1.integral_of_fun_eq_integral'
  条件: {f : α -> G} (hf : 可积 f μ)
  证明: by
  simp only [integral_eq_setToFun]
  exact setToFun_toL1 (dominatedFinMeasAdditive_weightedSMul μ) hf

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_toL1
-/
theorem L1.integral_of_fun_eq_integral' {f : α -> G} (hf : Integrable f μ) :
    ∫ a, (AEEqFun.mk f hf.aestronglyMeasurable) a ∂μ = ∫ a, f a ∂μ := by
  simp only [integral_eq_setToFun]
  exact setToFun_toL1 (dominatedFinMeasAdditive_weightedSMul μ) hf

/--
theorem `L1.integral_of_fun_eq_integral` / 定理 `L1.integral_of_fun_eq_integral`

English:
theorem L1.integral_of_fun_eq_integral
  given: {f : α -> G} (hf : Integrable f μ)
  proof: by
  simp [hf]

@[continuity]

中文:
定理 L1.integral_of_fun_eq_integral
  条件: {f : α -> G} (hf : 可积 f μ)
  证明: by
  simp [hf]

@[continuity]
-/
theorem L1.integral_of_fun_eq_integral {f : α -> G} (hf : Integrable f μ) :
    ∫ a, (hf.toL1 f) a ∂μ = ∫ a, f a ∂μ := by
  simp [hf]

@[continuity]
/--
theorem `continuous_integral` / 定理 `continuous_integral`

English:
theorem continuous_integral
  statement: Continuous fun f : α ->₁[μ] G => ∫ a, f a ∂μ
  proof: by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun (dominatedFinMeasAdditive_weightedSMul μ)

中文:
定理 continuous_integral
  结论: 连续 fun f : α ->₁[μ] G => ∫ a, f a ∂μ
  证明: by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun (dominatedFinMeasAdditive_weightedSMul μ)

Depends on / 依赖: continuous_setToFun, dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun
-/
theorem continuous_integral : Continuous fun f : α ->₁[μ] G => ∫ a, f a ∂μ := by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun (dominatedFinMeasAdditive_weightedSMul μ)

/--
theorem `norm_integral_le_lintegral_norm` / 定理 `norm_integral_le_lintegral_norm`

English:
theorem norm_integral_le_lintegral_norm
  given: (f : α -> G)
  proof: by
  simp only [integral_eq_setToFun]
  exact (norm_setToFun_le_toReal _ (by simp)).trans (by simp)

中文:
定理 norm_integral_le_lintegral_norm
  条件: (f : α -> G)
  证明: by
  simp only [integral_eq_setToFun]
  exact (norm_setToFun_le_toReal _ (by simp)).trans (by simp)

Depends on / 依赖: integral_eq_setToFun, norm_setToFun_le_toReal
-/
theorem norm_integral_le_lintegral_norm (f : α -> G) :
    ‖∫ a, f a ∂μ‖ <= ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  simp only [integral_eq_setToFun]
  exact (norm_setToFun_le_toReal _ (by simp)).trans (by simp)

/--
theorem `enorm_integral_le_lintegral_enorm` / 定理 `enorm_integral_le_lintegral_enorm`

English:
theorem enorm_integral_le_lintegral_enorm
  given: (f : α -> G)
  statement: ‖∫ a, f a ∂μ‖ₑ <= ∫⁻ a, ‖f a‖ₑ ∂μ
  proof: by
  simp only [integral_eq_setToFun]
  exact (enorm_setToFun_le _ (by simp)).trans (by simp)

中文:
定理 enorm_integral_le_lintegral_enorm
  条件: (f : α -> G)
  结论: ‖∫ a, f a ∂μ‖ₑ <= ∫⁻ a, ‖f a‖ₑ ∂μ
  证明: by
  simp only [integral_eq_setToFun]
  exact (enorm_setToFun_le _ (by simp)).trans (by simp)

Depends on / 依赖: enorm_setToFun_le, integral_eq_setToFun
-/
theorem enorm_integral_le_lintegral_enorm (f : α -> G) : ‖∫ a, f a ∂μ‖ₑ <= ∫⁻ a, ‖f a‖ₑ ∂μ := by
  simp only [integral_eq_setToFun]
  exact (enorm_setToFun_le _ (by simp)).trans (by simp)

/--
theorem `dist_integral_le_lintegral_edist` / 定理 `dist_integral_le_lintegral_edist`

English:
theorem dist_integral_le_lintegral_edist
  proof: by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]

中文:
定理 dist_integral_le_lintegral_edist
  证明: by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]

Depends on / 依赖: dist_eq_norm, edist_eq_enorm_sub, integral_sub, norm_integral_le_lintegral_norm
-/
theorem dist_integral_le_lintegral_edist
    {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (∫ a, f a ∂μ) (∫ a, g a ∂μ) <= (∫⁻ a, edist (f a) (g a) ∂μ).toReal := by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]

/--
theorem `edist_integral_le_lintegral_edist` / 定理 `edist_integral_le_lintegral_edist`

English:
theorem edist_integral_le_lintegral_edist
  proof: by
  rw [edist_dist]
  exact ENNReal.ofReal_le_of_le_toReal (dist_integral_le_lintegral_edist hf hg)

中文:
定理 edist_integral_le_lintegral_edist
  证明: by
  rw [edist_dist]
  exact ENNReal.ofReal_le_of_le_toReal (dist_integral_le_lintegral_edist hf hg)

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_of_le_toReal, dist_integral_le_lintegral_edist, edist_dist, ofReal_le_of_le_toReal
-/
theorem edist_integral_le_lintegral_edist
    {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) :
    edist (∫ a, f a ∂μ) (∫ a, g a ∂μ) <= ∫⁻ a, edist (f a) (g a) ∂μ := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_of_le_toReal (dist_integral_le_lintegral_edist hf hg)

/--
theorem `integral_eq_zero_of_ae` / 定理 `integral_eq_zero_of_ae`

English:
theorem integral_eq_zero_of_ae
  given: {f : α -> G} (hf : f =ᵐ[μ] 0)
  statement: ∫ a, f a ∂μ = 0
  proof: by
  simp [integral_congr_ae hf, integral_zero]

中文:
定理 integral_eq_zero_of_ae
  条件: {f : α -> G} (hf : f =ᵐ[μ] 0)
  结论: ∫ a, f a ∂μ = 0
  证明: by
  simp [integral_congr_ae hf, integral_zero]

Depends on / 依赖: integral_congr_ae, integral_zero
-/
theorem integral_eq_zero_of_ae {f : α -> G} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0 := by
  simp [integral_congr_ae hf, integral_zero]

/--
theorem `frequently_ae_ne_zero_of_integral_ne_zero` / 定理 `frequently_ae_ne_zero_of_integral_ne_zero`

English:
theorem frequently_ae_ne_zero_of_integral_ne_zero
  statement: {f : α -> G}
  proof: fun h' => h (integral_eq_zero_of_ae (h'.mono fun _ => not_not.mp))

中文:
定理 frequently_ae_ne_zero_of_integral_ne_zero
  结论: {f : α -> G}
  证明: fun h' => h (integral_eq_zero_of_ae (h'.mono fun _ => not_not.mp))

Depends on / 依赖: integral_eq_zero_of_ae, not_not, not_not.mp
-/
theorem frequently_ae_ne_zero_of_integral_ne_zero {f : α -> G}
    (h : ∫ a, f a ∂μ != 0) : existsᶠ a in ae μ, f a != 0 :=
  fun h' => h (integral_eq_zero_of_ae (h'.mono fun _ => not_not.mp))

/--
theorem `exists_ne_zero_of_integral_ne_zero` / 定理 `exists_ne_zero_of_integral_ne_zero`

English:
theorem exists_ne_zero_of_integral_ne_zero
  statement: {f : α -> G}
  proof: (frequently_ae_ne_zero_of_integral_ne_zero h).exists

中文:
定理 存在_ne_zero_of_integral_ne_zero
  结论: {f : α -> G}
  证明: (frequently_ae_ne_zero_of_integral_ne_zero h).exists

Depends on / 依赖: frequently_ae_ne_zero_of_integral_ne_zero
-/
theorem exists_ne_zero_of_integral_ne_zero {f : α -> G}
    (h : ∫ a, f a ∂μ != 0) : exists a, f a != 0 :=
  (frequently_ae_ne_zero_of_integral_ne_zero h).exists

/--
theorem `HasFiniteIntegral.tendsto_setIntegral_nhds_zero` / 定理 `HasFiniteIntegral.tendsto_setIntegral_nhds_zero`

English:
theorem HasFiniteIntegral.tendsto_setIntegral_nhds_zero
  statement: {ι} {f : α -> G}
  proof: by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_setLIntegral_zero (ne_of_lt hf) hs) (fun i => zero_le)
    fun i

中文:
定理 HasFinite整数egral.tendsto_set整数egral_nhds_zero
  结论: {ι} {f : α -> G}
  证明: by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_setLIntegral_zero (ne_of_lt hf) hs) (fun i => zero_le)
    fun i

Depends on / 依赖: ENNReal, ENNReal.coe_zero, ENNReal.tendsto_coe, NNReal, NNReal.coe_zero, NNReal.tendsto_coe, coe_nnnorm, coe_zero, enorm_integral_le_lintegral_enorm, ne_of_lt, simp_rw, tendsto_coe, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, tendsto_setLIntegral_zero, tendsto_zero_iff_norm_tendsto_zero, zero_le
-/
theorem HasFiniteIntegral.tendsto_setIntegral_nhds_zero {ι} {f : α -> G}
    (hf : HasFiniteIntegral f μ) {l : Filter ι} {s : ι -> Set α} (hs : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_setLIntegral_zero (ne_of_lt hf) hs) (fun i => zero_le)
    fun i => enorm_integral_le_lintegral_enorm _

/--
theorem `Integrable.tendsto_setIntegral_nhds_zero` / 定理 `Integrable.tendsto_setIntegral_nhds_zero`

English:
theorem Integrable.tendsto_setIntegral_nhds_zero
  statement: {ι} {f : α -> G} (hf : Integrable f μ)
  proof: hf.2.tendsto_setIntegral_nhds_zero hs

中文:
定理 可积.tendsto_set整数egral_nhds_zero
  结论: {ι} {f : α -> G} (hf : 可积 f μ)
  证明: hf.2.tendsto_setIntegral_nhds_zero hs

Depends on / 依赖: tendsto_setIntegral_nhds_zero
-/
theorem Integrable.tendsto_setIntegral_nhds_zero {ι} {f : α -> G} (hf : Integrable f μ)
    {l : Filter ι} {s : ι -> Set α} (hs : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) l (𝓝 0) :=
  hf.2.tendsto_setIntegral_nhds_zero hs

/--
theorem `tendsto_integral_of_L1` / 定理 `tendsto_integral_of_L1`

English:
theorem tendsto_integral_of_L1
  statement: {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ)
  proof: by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_of_L1 (dominatedFinMeasAdditive_weightedSMul μ) f hfi hFi hF

中文:
定理 tendsto_integral_of_L1
  结论: {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ)
  证明: by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_of_L1 (dominatedFinMeasAdditive_weightedSMul μ) f hfi hFi hF

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, tendsto_setToFun_of_L1
-/
theorem tendsto_integral_of_L1 {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ)
    {F : ι -> α -> G} {l : Filter ι} (hFi : forallᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) := by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_of_L1 (dominatedFinMeasAdditive_weightedSMul μ) f hfi hFi hF

/--
lemma `tendsto_integral_of_L1'` / 引理 `tendsto_integral_of_L1'`

English:
lemma tendsto_integral_of_L1'
  statement: {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ)
  proof: by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

中文:
引理 tendsto_integral_of_L1'
  结论: {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ)
  证明: by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

Depends on / 依赖: Pi.sub_apply, eLpNorm_one_eq_lintegral_enorm, simp_rw, sub_apply, tendsto_integral_of_L1
-/
lemma tendsto_integral_of_L1' {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ)
    {F : ι -> α -> G} {l : Filter ι} (hFi : forallᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

/--
lemma `tendsto_setIntegral_of_L1` / 引理 `tendsto_setIntegral_of_L1`

English:
lemma tendsto_setIntegral_of_L1
  statement: {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G}
  proof: by
  refine tendsto_integral_of_L1 f hfi.restrict ?_ ?_
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ Meas

中文:
引理 tendsto_set整数egral_of_L1
  结论: {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G}
  证明: by
  refine tendsto_integral_of_L1 f hfi.restrict ?_ ?_
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ Meas

Depends on / 依赖: Measure, Measure.restrict_le_self, eLpNorm_mono_measure, eLpNorm_one_eq_lintegral_enorm, filter_upwards, hfi.restrict, hi.restrict, restrict, restrict_le_self, simp_rw, tendsto_const_nhds, tendsto_integral_of_L1, tendsto_of_tendsto_of_tendsto_of_le_of_le, zero_le
-/
lemma tendsto_setIntegral_of_L1 {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G}
    {l : Filter ι}
    (hFi : forallᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0))
    (s : Set α) :
    Tendsto (fun i => ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi.restrict ?_ ?_
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)

/--
lemma `tendsto_setIntegral_of_L1'` / 引理 `tendsto_setIntegral_of_L1'`

English:
lemma tendsto_setIntegral_of_L1'
  statement: {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G}
  proof: by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

中文:
引理 tendsto_set整数egral_of_L1'
  结论: {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G}
  证明: by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

Depends on / 依赖: Pi.sub_apply, eLpNorm_one_eq_lintegral_enorm, simp_rw, sub_apply, tendsto_setIntegral_of_L1
-/
lemma tendsto_setIntegral_of_L1' {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G}
    {l : Filter ι} (hFi : forallᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0)) (s : Set α) :
    Tendsto (fun i => ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

/--
theorem `continuousWithinAt_of_dominated` / 定理 `continuousWithinAt_of_dominated`

English:
theorem continuousWithinAt_of_dominated
  statement: {F : X -> α -> G} {x₀ : X} {bound : α -> Real} {s : Set X}
  proof: by
  simp only [integral_eq_setToFun]
  exact continuousWithinAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

中文:
定理 continuousWithinAt_of_dominated
  结论: {F : X -> α -> G} {x₀ : X} {bound : α -> 实数} {s : 集合 X}
  证明: by
  simp only [integral_eq_setToFun]
  exact continuousWithinAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, continuousWithinAt_setToFun_of_dominated, dominatedFinMeasAdditive_weightedSMul, hF_meas, h_bound, h_cont, integral_eq_setToFun
-/
theorem continuousWithinAt_of_dominated {F : X -> α -> G} {x₀ : X} {bound : α -> Real} {s : Set X}
    (hF_meas : forallᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : forallᶠ x in 𝓝[s] x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a) (bound_integrable : Integrable bound μ)
    (h_cont : forallᵐ a ∂μ, ContinuousWithinAt (fun x => F x a) s x₀) :
    ContinuousWithinAt (fun x => ∫ a, F x a ∂μ) s x₀ := by
  simp only [integral_eq_setToFun]
  exact continuousWithinAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

/--
theorem `continuousAt_of_dominated` / 定理 `continuousAt_of_dominated`

English:
theorem continuousAt_of_dominated
  statement: {F : X -> α -> G} {x₀ : X} {bound : α -> Real}
  proof: by
  simp only [integral_eq_setToFun]
  exact continuousAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

中文:
定理 continuousAt_of_dominated
  结论: {F : X -> α -> G} {x₀ : X} {bound : α -> 实数}
  证明: by
  simp only [integral_eq_setToFun]
  exact continuousAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, continuousAt_setToFun_of_dominated, dominatedFinMeasAdditive_weightedSMul, hF_meas, h_bound, h_cont, integral_eq_setToFun
-/
theorem continuousAt_of_dominated {F : X -> α -> G} {x₀ : X} {bound : α -> Real}
    (hF_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : forallᶠ x in 𝓝 x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a) (bound_integrable : Integrable bound μ)
    (h_cont : forallᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x => ∫ a, F x a ∂μ) x₀ := by
  simp only [integral_eq_setToFun]
  exact continuousAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

/--
theorem `continuousOn_of_dominated` / 定理 `continuousOn_of_dominated`

English:
theorem continuousOn_of_dominated
  statement: {F : X -> α -> G} {bound : α -> Real} {s : Set X}
  proof: by
  simp only [integral_eq_setToFun]
  exact continuousOn_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

中文:
定理 continuousOn_of_dominated
  结论: {F : X -> α -> G} {bound : α -> 实数} {s : 集合 X}
  证明: by
  simp only [integral_eq_setToFun]
  exact continuousOn_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, continuousOn_setToFun_of_dominated, dominatedFinMeasAdditive_weightedSMul, hF_meas, h_bound, h_cont, integral_eq_setToFun
-/
theorem continuousOn_of_dominated {F : X -> α -> G} {bound : α -> Real} {s : Set X}
    (hF_meas : forall x in s, AEStronglyMeasurable (F x) μ)
    (h_bound : forall x in s, forallᵐ a ∂μ, ‖F x a‖ <= bound a) (bound_integrable : Integrable bound μ)
    (h_cont : forallᵐ a ∂μ, ContinuousOn (fun x => F x a) s) :
    ContinuousOn (fun x => ∫ a, F x a ∂μ) s := by
  simp only [integral_eq_setToFun]
  exact continuousOn_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

/--
theorem `continuous_of_dominated` / 定理 `continuous_of_dominated`

English:
theorem continuous_of_dominated
  statement: {F : X -> α -> G} {bound : α -> Real}
  proof: by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

中文:
定理 continuous_of_dominated
  结论: {F : X -> α -> G} {bound : α -> 实数}
  证明: by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, continuous_setToFun_of_dominated, dominatedFinMeasAdditive_weightedSMul, hF_meas, h_bound, h_cont, integral_eq_setToFun
-/
theorem continuous_of_dominated {F : X -> α -> G} {bound : α -> Real}
    (hF_meas : forall x, AEStronglyMeasurable (F x) μ) (h_bound : forall x, forallᵐ a ∂μ, ‖F x a‖ <= bound a)
    (bound_integrable : Integrable bound μ) (h_cont : forallᵐ a ∂μ, Continuous fun x => F x a) :
    Continuous fun x => ∫ a, F x a ∂μ := by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

/--
theorem `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` / 定理 `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`

English:
theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: by
  let f₁ := hf.toL1 f
  -- Go to the `L¹` space
  have eq₁ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) = ‖Lp.posPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_posPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁]; rw [h₂]; rw [ENNReal.

中文:
定理 integral_eq_lintegral_pos_part_sub_lintegral_neg_part
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: by
  let f₁ := hf.toL1 f
  -- Go to the `L¹` space
  have eq₁ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) = ‖Lp.posPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_posPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁]; rw [h₂]; rw [ENNReal.

Depends on / 依赖: hf.toL1
-/
theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part {f : α -> Real} (hf : Integrable f μ) :
    ∫ a, f a ∂μ =
      ENNReal.toReal (∫⁻ a, .ofReal (f a) ∂μ) - ENNReal.toReal (∫⁻ a, .ofReal (-f a) ∂μ) := by
  let f₁ := hf.toL1 f
  -- Go to the `L¹` space
  have eq₁ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) = ‖Lp.posPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_posPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁]; rw [h₂]; rw [ENNReal.ofReal]
    congr 1
    apply NNReal.eq
    rw [Real.nnnorm_of_nonneg (le_max_right _ _)]
    rw [Real.coe_toNNReal']; rw [NNReal.coe_mk]
  -- Go to the `L¹` space
  have eq₂ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (-f a) ∂μ) = ‖Lp.negPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_negPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁]; rw [h₂]; rw [ENNReal.ofReal]
    congr 1
    apply NNReal.eq
    simp only [Real.coe_toNNReal', coe_nnnorm, nnnorm_neg]
    rw [Real.norm_of_nonpos (min_le_right _ _)]; rw [← max_neg_neg]; rw [neg_zero]
  rw [eq₁]; rw [eq₂]; rw [integral]; rw [dif_pos]; rw [dif_pos]
  exact L1.integral_eq_norm_posPart_sub _

/--
theorem `integral_eq_lintegral_of_nonneg_ae` / 定理 `integral_eq_lintegral_of_nonneg_ae`

English:
theorem integral_eq_lintegral_of_nonneg_ae
  statement: {f : α -> Real} (hf : 0 <=ᵐ[μ] f)
  proof: by
  by_cases hfi : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
    have h_min : ∫⁻ a, ENNReal.ofReal (-f a) ∂μ = 0 := by
      rw [lintegral_eq_zero_iff']
      · refine hf.mono ?_
        simp only [Pi.zero_apply]
        intro a h
        simp only [h, neg_no

中文:
定理 integral_eq_lintegral_of_nonneg_ae
  结论: {f : α -> 实数} (hf : 0 <=ᵐ[μ] f)
  证明: by
  by_cases hfi : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
    have h_min : ∫⁻ a, ENNReal.ofReal (-f a) ∂μ = 0 := by
      rw [lintegral_eq_zero_iff']
      · refine hf.mono ?_
        simp only [Pi.zero_apply]
        intro a h
        simp only [h, neg_no

Depends on / 依赖: ENNReal, ENNReal.ofReal, Integrable, Pi.zero_apply, _root_, _root_.sub_zero, aemeasurable, comp_aemeasurable, h_min, hasFiniteIntegral_iff_norm, hf.mono, hfm.aemeasurable.neg, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, integral_undef, lintegral_eq_zero_iff, lt_top_iff_ne_top, measurable_ofReal, measurable_ofReal.comp_aemeasurable, neg_nonpos, ofReal
-/
theorem integral_eq_lintegral_of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f)
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
    rw [h_min]; rw [toReal_zero]; rw [_root_.sub_zero]
  · rw [integral_undef hfi]
    simp_rw [Integrable, hfm, hasFiniteIntegral_iff_norm, lt_top_iff_ne_top, Ne, true_and,
      Classical.not_not] at hfi
    have : ∫⁻ a : α, ENNReal.ofReal (f a) ∂μ = ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ := by
      refine lintegral_congr_ae (hf.mono fun a h => ?_)
      dsimp only
      rw [Real.norm_eq_abs]; rw [abs_of_nonneg h]
    rw [this]; rw [hfi]; rw [toReal_top]

/--
theorem `integral_norm_eq_lintegral_enorm` / 定理 `integral_norm_eq_lintegral_enorm`

English:
theorem integral_norm_eq_lintegral_enorm
  statement: {P : Type*} [NormedAddCommGroup P] {f : α -> P}
  proof: by
  rw [integral_eq_lintegral_of_nonneg_ae _ hf.norm]
  · simp_rw [ofReal_norm]
  · filter_upwards; simp_rw [Pi.zero_apply, norm_nonneg, imp_true_iff]

中文:
定理 integral_norm_eq_lintegral_enorm
  结论: {P : 类型} [赋范交换加群 P] {f : α -> P}
  证明: by
  rw [integral_eq_lintegral_of_nonneg_ae _ hf.norm]
  · simp_rw [ofReal_norm]
  · filter_upwards; simp_rw [Pi.zero_apply, norm_nonneg, imp_true_iff]

Depends on / 依赖: Pi.zero_apply, filter_upwards, hf.norm, imp_true_iff, integral_eq_lintegral_of_nonneg_ae, norm_nonneg, ofReal_norm, simp_rw, zero_apply
-/
theorem integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α -> P}
    (hf : AEStronglyMeasurable f μ) : ∫ x, ‖f x‖ ∂μ = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hf.norm]
  · simp_rw [ofReal_norm]
  · filter_upwards; simp_rw [Pi.zero_apply, norm_nonneg, imp_true_iff]

/--
theorem `ofReal_integral_norm_eq_lintegral_enorm` / 定理 `ofReal_integral_norm_eq_lintegral_enorm`

English:
theorem ofReal_integral_norm_eq_lintegral_enorm
  statement: {P : Type*} [NormedAddCommGroup P] {f : α -> P}
  proof: by
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]; rw [ENNReal.ofReal_toReal]
  exact lt_top_iff_ne_top.mp (hasFiniteIntegral_iff_enorm.mpr hf.2)

中文:
定理 of实数_integral_norm_eq_lintegral_enorm
  结论: {P : 类型} [赋范交换加群 P] {f : α -> P}
  证明: by
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]; rw [ENNReal.ofReal_toReal]
  exact lt_top_iff_ne_top.mp (hasFiniteIntegral_iff_enorm.mpr hf.2)

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, aestronglyMeasurable, hasFiniteIntegral_iff_enorm, hasFiniteIntegral_iff_enorm.mpr, hf.aestronglyMeasurable, integral_norm_eq_lintegral_enorm, lt_top_iff_ne_top, lt_top_iff_ne_top.mp, ofReal_toReal
-/
theorem ofReal_integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α -> P}
    (hf : Integrable f μ) : ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]; rw [ENNReal.ofReal_toReal]
  exact lt_top_iff_ne_top.mp (hasFiniteIntegral_iff_enorm.mpr hf.2)

/--
theorem `SimpleFunc.integral_eq_integral` / 定理 `SimpleFunc.integral_eq_integral`

English:
theorem SimpleFunc.integral_eq_integral
  given: [CompleteSpace E] (f : α ->ₛ E) (hfi : Integrable f μ)
  proof: by
  rw [MeasureTheory.integral_eq f hfi]; rw [← L1.SimpleFunc.toLp_one_eq_toL1]; rw [L1.SimpleFunc.integral_L1_eq_integral]; rw [L1.SimpleFunc.integral_eq_integral]
  exact SimpleFunc.integral_congr hfi (Lp.simpleFunc.toSimpleFunc_toLp _ _).symm

中文:
定理 SimpleFunc.integral_eq_integral
  条件: [完备空间 E] (f : α ->ₛ E) (hfi : 可积 f μ)
  证明: by
  rw [MeasureTheory.integral_eq f hfi]; rw [← L1.SimpleFunc.toLp_one_eq_toL1]; rw [L1.SimpleFunc.integral_L1_eq_integral]; rw [L1.SimpleFunc.integral_eq_integral]
  exact SimpleFunc.integral_congr hfi (Lp.simpleFunc.toSimpleFunc_toLp _ _).symm

Depends on / 依赖: L1.SimpleFunc.integral_L1_eq_integral, L1.SimpleFunc.integral_eq_integral, L1.SimpleFunc.toLp_one_eq_toL1, Lp.simpleFunc.toSimpleFunc_toLp, MeasureTheory, MeasureTheory.integral_eq, SimpleFunc, SimpleFunc.integral_congr, integral_L1_eq_integral, integral_congr, integral_eq, integral_eq_integral, simpleFunc, toLp_one_eq_toL1, toSimpleFunc_toLp
-/
theorem SimpleFunc.integral_eq_integral [CompleteSpace E] (f : α ->ₛ E) (hfi : Integrable f μ) :
    f.integral μ = ∫ x, f x ∂μ := by
  rw [MeasureTheory.integral_eq f hfi]; rw [← L1.SimpleFunc.toLp_one_eq_toL1]; rw [L1.SimpleFunc.integral_L1_eq_integral]; rw [L1.SimpleFunc.integral_eq_integral]
  exact SimpleFunc.integral_congr hfi (Lp.simpleFunc.toSimpleFunc_toLp _ _).symm

/--
theorem `SimpleFunc.integral_eq_sum` / 定理 `SimpleFunc.integral_eq_sum`

English:
theorem SimpleFunc.integral_eq_sum
  given: [CompleteSpace E] (f : α ->ₛ E) (hfi : Integrable f μ)
  proof: by
  rw [← f.integral_eq_integral hfi]; rw [SimpleFunc.integral]; rw [← SimpleFunc.integral_eq]; rfl

中文:
定理 SimpleFunc.integral_eq_sum
  条件: [完备空间 E] (f : α ->ₛ E) (hfi : 可积 f μ)
  证明: by
  rw [← f.integral_eq_integral hfi]; rw [SimpleFunc.integral]; rw [← SimpleFunc.integral_eq]; rfl

Depends on / 依赖: SimpleFunc, SimpleFunc.integral, SimpleFunc.integral_eq, f.integral_eq_integral, integral, integral_eq, integral_eq_integral
-/
theorem SimpleFunc.integral_eq_sum [CompleteSpace E] (f : α ->ₛ E) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x in f.range, μ.real (f ⁻¹' {x}) • x := by
  rw [← f.integral_eq_integral hfi]; rw [SimpleFunc.integral]; rw [← SimpleFunc.integral_eq]; rfl

/--
theorem `tendsto_integral_approxOn_of_measurable` / 定理 `tendsto_integral_approxOn_of_measurable`

English:
theorem tendsto_integral_approxOn_of_measurable
  statement: [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  proof: by
  have hfi' := SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i
  simp only [SimpleFunc.integral_eq_integral _ (hfi' _), integral, L1.integral]
  exact tendsto_setToFun_approxOn_of_measurable (dominatedFinMeasAdditive_weightedSMul μ)
    hfi hfm hs h₀ h₀i

中文:
定理 tendsto_integral_approxOn_of_measurable
  结论: [完备空间 E] [可测空间 E] [Borel空间 E]
  证明: by
  have hfi' := SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i
  simp only [SimpleFunc.integral_eq_integral _ (hfi' _), integral, L1.integral]
  exact tendsto_setToFun_approxOn_of_measurable (dominatedFinMeasAdditive_weightedSMul μ)
    hfi hfm hs h₀ h₀i

Depends on / 依赖: L1.integral, SimpleFunc, SimpleFunc.integrable_approxOn, SimpleFunc.integral_eq_integral, dominatedFinMeasAdditive_weightedSMul, integrable_approxOn, integral, integral_eq_integral, tendsto_setToFun_approxOn_of_measurable
-/
theorem tendsto_integral_approxOn_of_measurable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : α -> E} {s : Set E} [SeparableSpace s] (hfi : Integrable f μ) (hfm : Measurable f)
    (hs : forallᵐ x ∂μ, f x in closure s) {y₀ : E} (h₀ : y₀ in s) (h₀i : Integrable (fun _ => y₀) μ) :
    Tendsto (fun n => (SimpleFunc.approxOn f hfm s y₀ h₀ n).integral μ)
      atTop (𝓝 <| ∫ x, f x ∂μ) := by
  have hfi' := SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i
  simp only [SimpleFunc.integral_eq_integral _ (hfi' _), integral, L1.integral]
  exact tendsto_setToFun_approxOn_of_measurable (dominatedFinMeasAdditive_weightedSMul μ)
    hfi hfm hs h₀ h₀i

/--
theorem `tendsto_integral_approxOn_of_measurable_of_range_subset` / 定理 `tendsto_integral_approxOn_of_measurable_of_range_subset`

English:
theorem tendsto_integral_approxOn_of_measurable_of_range_subset
  proof: by
  apply tendsto_integral_approxOn_of_measurable hf fmeas _ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

中文:
定理 tendsto_integral_approxOn_of_measurable_of_range_subset
  证明: by
  apply tendsto_integral_approxOn_of_measurable hf fmeas _ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

Depends on / 依赖: Eventually, Eventually.of_forall, Set.mem_union_left, integrable_zero, mem_range_self, mem_union_left, of_forall, subset_closure, tendsto_integral_approxOn_of_measurable
-/
theorem tendsto_integral_approxOn_of_measurable_of_range_subset
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : α -> E} (fmeas : Measurable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s]
    (hs : range f union {0} subseteq s) :
    Tendsto (fun n => (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n).integral μ) atTop
      (𝓝 <| ∫ x, f x ∂μ) := by
  apply tendsto_integral_approxOn_of_measurable hf fmeas _ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

-- We redeclare `E` here to temporarily avoid
-- the `[NormedSpace ℝ E]` instance.
/--
theorem `tendsto_integral_norm_approxOn_sub` / 定理 `tendsto_integral_norm_approxOn_sub`

English:
theorem tendsto_integral_norm_approxOn_sub
  proof: by
  convert! (tendsto_toReal zero_ne_top).comp (tendsto_approxOn_range_L1_enorm fmeas hf) with n
  rw [integral_norm_eq_lintegral_enorm]
  · simp
  · apply (SimpleFunc.aestronglyMeasurable _).sub
    apply (stronglyMeasurable_iff_measurable_separable.2 ⟨fmeas, ?_⟩).aestronglyMeasurable
    exact .m

中文:
定理 tendsto_integral_norm_approxOn_sub
  证明: by
  convert! (tendsto_toReal zero_ne_top).comp (tendsto_approxOn_range_L1_enorm fmeas hf) with n
  rw [integral_norm_eq_lintegral_enorm]
  · simp
  · apply (SimpleFunc.aestronglyMeasurable _).sub
    apply (stronglyMeasurable_iff_measurable_separable.2 ⟨fmeas, ?_⟩).aestronglyMeasurable
    exact .m

Depends on / 依赖: SimpleFunc, SimpleFunc.aestronglyMeasurable, aestronglyMeasurable, convert, integral_norm_eq_lintegral_enorm, of_subtype, stronglyMeasurable_iff_measurable_separable, subset_union_left, tendsto_approxOn_range_L1_enorm, tendsto_toReal, zero_ne_top
-/
theorem tendsto_integral_norm_approxOn_sub
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {f : α -> E}
    (fmeas : Measurable f) (hf : Integrable f μ) [SeparableSpace (range f union {0} : Set E)] :
    Tendsto (fun n => ∫ x, ‖SimpleFunc.approxOn f fmeas (range f union {0}) 0 (by simp) n x - f x‖ ∂μ)
      atTop (𝓝 0) := by
  convert! (tendsto_toReal zero_ne_top).comp (tendsto_approxOn_range_L1_enorm fmeas hf) with n
  rw [integral_norm_eq_lintegral_enorm]
  · simp
  · apply (SimpleFunc.aestronglyMeasurable _).sub
    apply (stronglyMeasurable_iff_measurable_separable.2 ⟨fmeas, ?_⟩).aestronglyMeasurable
    exact .mono (.of_subtype (range f union {0})) subset_union_left

/--
theorem `integral_eq_integral_pos_part_sub_integral_neg_part` / 定理 `integral_eq_integral_pos_part_sub_integral_neg_part`

English:
theorem integral_eq_integral_pos_part_sub_integral_neg_part
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: by
  rw [← integral_sub hf.real_toNNReal]
  · simp
  · exact hf.neg.real_toNNReal

中文:
定理 integral_eq_integral_pos_part_sub_integral_neg_part
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: by
  rw [← integral_sub hf.real_toNNReal]
  · simp
  · exact hf.neg.real_toNNReal

Depends on / 依赖: hf.neg.real_toNNReal, hf.real_toNNReal, integral_sub, real_toNNReal
-/
theorem integral_eq_integral_pos_part_sub_integral_neg_part {f : α -> Real} (hf : Integrable f μ) :
    ∫ a, f a ∂μ = ∫ a, (Real.toNNReal (f a) : Real) ∂μ - ∫ a, (Real.toNNReal (-f a) : Real) ∂μ := by
  rw [← integral_sub hf.real_toNNReal]
  · simp
  · exact hf.neg.real_toNNReal

/--
theorem `integral_abs_eq_two_mul_integral_posPart_sub_integral` / 定理 `integral_abs_eq_two_mul_integral_posPart_sub_integral`

English:
theorem integral_abs_eq_two_mul_integral_posPart_sub_integral
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: by
  simp only [PosPart.posPart]
  have h_eq : forall x, |f x| = 2 * max (f x) 0 - f x := by grind
  rw [integral_congr_ae (Eventually.of_forall h_eq)]; rw [integral_sub (by fun_prop) hf]; rw [integral_const_mul]

中文:
定理 integral_abs_eq_two_mul_integral_posPart_sub_integral
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: by
  simp only [PosPart.posPart]
  have h_eq : forall x, |f x| = 2 * max (f x) 0 - f x := by grind
  rw [integral_congr_ae (Eventually.of_forall h_eq)]; rw [integral_sub (by fun_prop) hf]; rw [integral_const_mul]

Depends on / 依赖: Eventually, Eventually.of_forall, PosPart, PosPart.posPart, fun_prop, h_eq, integral_congr_ae, integral_const_mul, integral_sub, of_forall, posPart
-/
theorem integral_abs_eq_two_mul_integral_posPart_sub_integral {f : α -> Real} (hf : Integrable f μ) :
    ∫ x, |f x| ∂μ = 2 * ∫ x, (f x)⁺ ∂μ - ∫ x, f x ∂μ := by
  simp only [PosPart.posPart]
  have h_eq : forall x, |f x| = 2 * max (f x) 0 - f x := by grind
  rw [integral_congr_ae (Eventually.of_forall h_eq)]; rw [integral_sub (by fun_prop) hf]; rw [integral_const_mul]

/--
theorem `integral_abs_eq_two_mul_integral_negPart_add_integral` / 定理 `integral_abs_eq_two_mul_integral_negPart_add_integral`

English:
theorem integral_abs_eq_two_mul_integral_negPart_add_integral
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: by
  simp only [NegPart.negPart]
  have h_eq : forall x, |f x| = 2 * max (-f x) 0 + f x := by grind
  rw [integral_congr_ae (Eventually.of_forall h_eq)]; rw [integral_add (by fun_prop) hf]; rw [integral_const_mul]

中文:
定理 integral_abs_eq_two_mul_integral_negPart_add_integral
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: by
  simp only [NegPart.negPart]
  have h_eq : forall x, |f x| = 2 * max (-f x) 0 + f x := by grind
  rw [integral_congr_ae (Eventually.of_forall h_eq)]; rw [integral_add (by fun_prop) hf]; rw [integral_const_mul]

Depends on / 依赖: Eventually, Eventually.of_forall, NegPart, NegPart.negPart, fun_prop, h_eq, integral_add, integral_congr_ae, integral_const_mul, negPart, of_forall
-/
theorem integral_abs_eq_two_mul_integral_negPart_add_integral {f : α -> Real} (hf : Integrable f μ) :
    ∫ x, |f x| ∂μ = 2 * ∫ x, (f x)⁻ ∂μ + ∫ x, f x ∂μ := by
  simp only [NegPart.negPart]
  have h_eq : forall x, |f x| = 2 * max (-f x) 0 + f x := by grind
  rw [integral_congr_ae (Eventually.of_forall h_eq)]; rw [integral_add (by fun_prop) hf]; rw [integral_const_mul]

end Basic

section Order

variable [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule Real E]

@[gcongr]
/--
lemma `integral_mono_measure` / 引理 `integral_mono_measure`

English:
lemma integral_mono_measure
  statement: [OrderClosedTopology E] {f : α -> E} {ν : Measure α} (hle : μ <= ν)
  proof: by
  by_cases hE : CompleteSpace E
  swap; · simp [integral, hE]
  borelize E
  obtain ⟨g, hg, hg_nonneg, hfg⟩ := hfi.1.exists_stronglyMeasurable_range_subset
    isClosed_Ici.measurableSet (Set.nonempty_Ici (a := 0)) hf
  rw [integrable_congr hfg] at hfi
  simp only [integral_congr_ae hfg, integral

中文:
引理 integral_mono_measure
  结论: [OrderClosed拓扑 E] {f : α -> E} {ν : 测度 α} (hle : μ <= ν)
  证明: by
  by_cases hE : CompleteSpace E
  swap; · simp [integral, hE]
  borelize E
  obtain ⟨g, hg, hg_nonneg, hfg⟩ := hfi.1.exists_stronglyMeasurable_range_subset
    isClosed_Ici.measurableSet (Set.nonempty_Ici (a := 0)) hf
  rw [integrable_congr hfg] at hfi
  simp only [integral_congr_ae hfg, integral

Depends on / 依赖: CompleteSpace, Set.nonempty_Ici, ae_mono, borelize, exists_stronglyMeasurable_range_subset, hg.measurable, hg.separableSpace_range_union_singleton, hg_nonneg, integrable_congr, integral, integral_congr_ae, isClosed_Ici, isClosed_Ici.measurableSet, le_rfl, measurable, measurableSet, nonempty_Ici, separableSpace_range_union_singleton, tendsto_integral_approx, tendsto_integral_approxOn_of_measurable_of_range_subset
-/
lemma integral_mono_measure [OrderClosedTopology E] {f : α -> E} {ν : Measure α} (hle : μ <= ν)
    (hf : 0 <=ᵐ[ν] f) (hfi : Integrable f ν) : ∫ (a : α), f a ∂μ <= ∫ (a : α), f a ∂ν := by
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
  exact fun n => SimpleFunc.integral_mono_measure
    (Eventually.of_forall <| SimpleFunc.approxOn_range_nonneg hg_nonneg n) hle
    (SimpleFunc.integrable_approxOn_range _ hfi n)

variable [ClosedIciTopology E]

/--
lemma `integral_nonneg_of_ae` / 引理 `integral_nonneg_of_ae`

English:
lemma integral_nonneg_of_ae
  given: {f : α -> E} (hf : 0 <=ᵐ[μ] f)
  proof: integral_eq_setToFun f ▸ setToFun_nonneg (dominatedFinMeasAdditive_weightedSMul μ)
    (fun s _ _ => weightedSMul_nonneg s) hf

中文:
引理 integral_nonneg_of_ae
  条件: {f : α -> E} (hf : 0 <=ᵐ[μ] f)
  证明: integral_eq_setToFun f ▸ setToFun_nonneg (dominatedFinMeasAdditive_weightedSMul μ)
    (fun s _ _ => weightedSMul_nonneg s) hf

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_nonneg, weightedSMul_nonneg
-/
lemma integral_nonneg_of_ae {f : α -> E} (hf : 0 <=ᵐ[μ] f) :
    0 <= ∫ x, f x ∂μ :=
  integral_eq_setToFun f ▸ setToFun_nonneg (dominatedFinMeasAdditive_weightedSMul μ)
    (fun s _ _ => weightedSMul_nonneg s) hf

/--
lemma `integral_nonneg` / 引理 `integral_nonneg`

English:
lemma integral_nonneg
  given: {f : α -> E} (hf : 0 <= f)
  proof: integral_nonneg_of_ae (ae_of_all _ hf)

中文:
引理 integral_nonneg
  条件: {f : α -> E} (hf : 0 <= f)
  证明: integral_nonneg_of_ae (ae_of_all _ hf)

Depends on / 依赖: ae_of_all, integral_nonneg_of_ae
-/
lemma integral_nonneg {f : α -> E} (hf : 0 <= f) :
    0 <= ∫ x, f x ∂μ :=
  integral_nonneg_of_ae (ae_of_all _ hf)

/--
lemma `integral_nonpos_of_ae` / 引理 `integral_nonpos_of_ae`

English:
lemma integral_nonpos_of_ae
  given: {f : α -> E} (hf : f <=ᵐ[μ] 0)
  proof: by
  rw [← neg_nonneg]; rw [← integral_neg]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf] with x hx
  simpa

中文:
引理 integral_nonpos_of_ae
  条件: {f : α -> E} (hf : f <=ᵐ[μ] 0)
  证明: by
  rw [← neg_nonneg]; rw [← integral_neg]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf] with x hx
  simpa

Depends on / 依赖: filter_upwards, integral_neg, integral_nonneg_of_ae, neg_nonneg
-/
lemma integral_nonpos_of_ae {f : α -> E} (hf : f <=ᵐ[μ] 0) :
    ∫ x, f x ∂μ <= 0 := by
  rw [← neg_nonneg]; rw [← integral_neg]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf] with x hx
  simpa

/--
lemma `integral_nonpos` / 引理 `integral_nonpos`

English:
lemma integral_nonpos
  given: {f : α -> E} (hf : f <= 0)
  proof: integral_nonpos_of_ae (ae_of_all _ hf)

中文:
引理 integral_nonpos
  条件: {f : α -> E} (hf : f <= 0)
  证明: integral_nonpos_of_ae (ae_of_all _ hf)

Depends on / 依赖: ae_of_all, integral_nonpos_of_ae
-/
lemma integral_nonpos {f : α -> E} (hf : f <= 0) :
    ∫ x, f x ∂μ <= 0 :=
  integral_nonpos_of_ae (ae_of_all _ hf)

/--
lemma `integral_mono_ae` / 引理 `integral_mono_ae`

English:
lemma integral_mono_ae
  statement: {f g : α -> E} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: by
  rw [← sub_nonneg]; rw [← integral_sub hg hf]
  refine integral_nonneg_of_ae ?_
  filter_upwards [h] with x hx
  simpa

@[gcongr, mono]

中文:
引理 integral_mono_ae
  结论: {f g : α -> E} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: by
  rw [← sub_nonneg]; rw [← integral_sub hg hf]
  refine integral_nonneg_of_ae ?_
  filter_upwards [h] with x hx
  simpa

@[gcongr, mono]

Depends on / 依赖: filter_upwards, integral_nonneg_of_ae, integral_sub, sub_nonneg
-/
lemma integral_mono_ae {f g : α -> E} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ := by
  rw [← sub_nonneg]; rw [← integral_sub hg hf]
  refine integral_nonneg_of_ae ?_
  filter_upwards [h] with x hx
  simpa

@[gcongr, mono]
/--
lemma `integral_mono` / 引理 `integral_mono`

English:
lemma integral_mono
  statement: {f g : α -> E} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: integral_mono_ae hf hg (ae_of_all _ h)

中文:
引理 integral_mono
  结论: {f g : α -> E} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: integral_mono_ae hf hg (ae_of_all _ h)

Depends on / 依赖: ae_of_all, integral_mono_ae
-/
lemma integral_mono {f g : α -> E} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ :=
  integral_mono_ae hf hg (ae_of_all _ h)

/--
lemma `integral_mono_of_nonneg` / 引理 `integral_mono_of_nonneg`

English:
lemma integral_mono_of_nonneg
  statement: {f g : α -> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable g μ)
  proof: by
  by_cases hfi : Integrable f μ
  · exact integral_mono_ae hfi hgi h
  · exact integral_undef hfi ▸ integral_nonneg_of_ae (hf.trans h)

中文:
引理 integral_mono_of_nonneg
  结论: {f g : α -> E} (hf : 0 <=ᵐ[μ] f) (hgi : 可积 g μ)
  证明: by
  by_cases hfi : Integrable f μ
  · exact integral_mono_ae hfi hgi h
  · exact integral_undef hfi ▸ integral_nonneg_of_ae (hf.trans h)

Depends on / 依赖: Integrable, hf.trans, integral_mono_ae, integral_nonneg_of_ae, integral_undef
-/
lemma integral_mono_of_nonneg {f g : α -> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable g μ)
    (h : f <=ᵐ[μ] g) : ∫ a, f a ∂μ <= ∫ a, g a ∂μ := by
  by_cases hfi : Integrable f μ
  · exact integral_mono_ae hfi hgi h
  · exact integral_undef hfi ▸ integral_nonneg_of_ae (hf.trans h)

/--
lemma `integral_monotoneOn_of_integrand_ae` / 引理 `integral_monotoneOn_of_integrand_ae`

English:
lemma integral_monotoneOn_of_integrand_ae
  statement: {β : Type*} [Preorder β] {f : α -> β -> E}
  proof: by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int a ha) (hf_int b hb) ?_
  filter_upwards [hf_mono] with x hx
  exact hx ha hb hab

中文:
引理 integral_monotoneOn_of_integrand_ae
  结论: {β : 类型} [预序 β] {f : α -> β -> E}
  证明: by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int a ha) (hf_int b hb) ?_
  filter_upwards [hf_mono] with x hx
  exact hx ha hb hab

Depends on / 依赖: filter_upwards, hf_int, hf_mono, integral_mono_ae
-/
lemma integral_monotoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : α -> β -> E}
    {s : Set β} (hf_mono : forallᵐ x ∂μ, MonotoneOn (f x) s)
    (hf_int : forall a in s, Integrable (f · a) μ) : MonotoneOn (fun b => ∫ x, f x b ∂μ) s := by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int a ha) (hf_int b hb) ?_
  filter_upwards [hf_mono] with x hx
  exact hx ha hb hab

/--
lemma `integral_antitoneOn_of_integrand_ae` / 引理 `integral_antitoneOn_of_integrand_ae`

English:
lemma integral_antitoneOn_of_integrand_ae
  statement: {β : Type*} [Preorder β] {f : α -> β -> E}
  proof: by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int b hb) (hf_int a ha) ?_
  filter_upwards [hf_anti] with x hx
  exact hx ha hb hab

中文:
引理 integral_antitoneOn_of_integrand_ae
  结论: {β : 类型} [预序 β] {f : α -> β -> E}
  证明: by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int b hb) (hf_int a ha) ?_
  filter_upwards [hf_anti] with x hx
  exact hx ha hb hab

Depends on / 依赖: filter_upwards, hf_anti, hf_int, integral_mono_ae
-/
lemma integral_antitoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : α -> β -> E}
    {s : Set β} (hf_anti : forallᵐ x ∂μ, AntitoneOn (f x) s)
    (hf_int : forall a in s, Integrable (f · a) μ) : AntitoneOn (fun b => ∫ x, f x b ∂μ) s := by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int b hb) (hf_int a ha) ?_
  filter_upwards [hf_anti] with x hx
  exact hx ha hb hab

/--
lemma `integral_convexOn_of_integrand_ae` / 引理 `integral_convexOn_of_integrand_ae`

English:
lemma integral_convexOn_of_integrand_ae
  statement: {β : Type*} [AddCommMonoid β]
  proof: by
  refine ⟨hs, ?_⟩
  intro a ha b hb p q hp hq hpq
  calc ∫ x, f x (p • a + q • b) ∂μ <= ∫ x, p • f x a + q • f x b ∂μ := by
                  refine integral_mono_ae ?lhs ?rhs ?ae_le
                  case lhs =>
                    refine hf_int _ ?_
                    rw [convex_iff_add_mem] a

中文:
引理 integral_convexOn_of_integrand_ae
  结论: {β : 类型} [加法交换幺半群 β]
  证明: by
  refine ⟨hs, ?_⟩
  intro a ha b hb p q hp hq hpq
  calc ∫ x, f x (p • a + q • b) ∂μ <= ∫ x, p • f x a + q • f x b ∂μ := by
                  refine integral_mono_ae ?lhs ?rhs ?ae_le
                  case lhs =>
                    refine hf_int _ ?_
                    rw [convex_iff_add_mem] a

Depends on / 依赖: ae_le, all_goals, convex_iff_add_mem, filter_upwards, fun_prop, hf_conv, hf_int, integral_add, integral_mono_ae
-/
lemma integral_convexOn_of_integrand_ae {β : Type*} [AddCommMonoid β]
    [Module Real β] {f : α -> β -> E} {s : Set β} (hs : Convex Real s)
    (hf_conv : forallᵐ x ∂μ, ConvexOn Real s (f x)) (hf_int : forall a in s, Integrable (f · a) μ) :
    ConvexOn Real s (fun b => ∫ x, f x b ∂μ) := by
  refine ⟨hs, ?_⟩
  intro a ha b hb p q hp hq hpq
  calc ∫ x, f x (p • a + q • b) ∂μ <= ∫ x, p • f x a + q • f x b ∂μ := by
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

/--
lemma `integral_concaveOn_of_integrand_ae` / 引理 `integral_concaveOn_of_integrand_ae`

English:
lemma integral_concaveOn_of_integrand_ae
  statement: {β : Type*} [AddCommMonoid β]
  proof: by
  simp_rw [← neg_convexOn_iff] at hf_conc ⊢
  simpa only [Pi.neg_apply, integral_neg] using!
    integral_convexOn_of_integrand_ae hs hf_conc (hf_int · · |>.neg)

中文:
引理 integral_concaveOn_of_integrand_ae
  结论: {β : 类型} [加法交换幺半群 β]
  证明: by
  simp_rw [← neg_convexOn_iff] at hf_conc ⊢
  simpa only [Pi.neg_apply, integral_neg] using!
    integral_convexOn_of_integrand_ae hs hf_conc (hf_int · · |>.neg)

Depends on / 依赖: Pi.neg_apply, hf_conc, hf_int, integral_convexOn_of_integrand_ae, integral_neg, neg_apply, neg_convexOn_iff, simp_rw
-/
lemma integral_concaveOn_of_integrand_ae {β : Type*} [AddCommMonoid β]
    [Module Real β] {f : α -> β -> E} {s : Set β} (hs : Convex Real s)
    (hf_conc : forallᵐ x ∂μ, ConcaveOn Real s (f x)) (hf_int : forall a in s, Integrable (f · a) μ) :
    ConcaveOn Real s (fun b => ∫ x, f x b ∂μ) := by
  simp_rw [← neg_convexOn_iff] at hf_conc ⊢
  simpa only [Pi.neg_apply, integral_neg] using!
    integral_convexOn_of_integrand_ae hs hf_conc (hf_int · · |>.neg)

end Order

variable [hE : CompleteSpace E]

/--
theorem `lintegral_coe_eq_integral` / 定理 `lintegral_coe_eq_integral`

English:
theorem lintegral_coe_eq_integral
  given: (f : α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ)
  proof: by
  simp_rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (f x).coe_nonneg)
      hfi.aestronglyMeasurable, ← ENNReal.coe_nnreal_eq]
  rw [ENNReal.ofReal_toReal]
  simpa [← lt_top_iff_ne_top, hasFiniteIntegral_iff_enorm, NNReal.enorm_eq] using
    hfi.hasFiniteIntegral

中文:
定理 lintegral_coe_eq_integral
  条件: (f : α -> 实数>=0) (hfi : 可积 (fun x => (f x : 实数)) μ)
  证明: by
  simp_rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (f x).coe_nonneg)
      hfi.aestronglyMeasurable, ← ENNReal.coe_nnreal_eq]
  rw [ENNReal.ofReal_toReal]
  simpa [← lt_top_iff_ne_top, hasFiniteIntegral_iff_enorm, NNReal.enorm_eq] using
    hfi.hasFiniteIntegral

Depends on / 依赖: ENNReal, ENNReal.coe_nnreal_eq, ENNReal.ofReal_toReal, Eventually, Eventually.of_forall, NNReal, NNReal.enorm_eq, aestronglyMeasurable, coe_nnreal_eq, coe_nonneg, enorm_eq, hasFiniteIntegral, hasFiniteIntegral_iff_enorm, hfi.aestronglyMeasurable, hfi.hasFiniteIntegral, integral_eq_lintegral_of_nonneg_ae, lt_top_iff_ne_top, ofReal_toReal, of_forall, simp_rw
-/
theorem lintegral_coe_eq_integral (f : α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ) :
    ∫⁻ a, f a ∂μ = ENNReal.ofReal (∫ a, f a ∂μ) := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (f x).coe_nonneg)
      hfi.aestronglyMeasurable, ← ENNReal.coe_nnreal_eq]
  rw [ENNReal.ofReal_toReal]
  simpa [← lt_top_iff_ne_top, hasFiniteIntegral_iff_enorm, NNReal.enorm_eq] using
    hfi.hasFiniteIntegral

/--
theorem `ofReal_integral_eq_lintegral_ofReal` / 定理 `ofReal_integral_eq_lintegral_ofReal`

English:
theorem ofReal_integral_eq_lintegral_ofReal
  given: {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f)
  proof: by
  have : f =ᵐ[μ] (‖f ·‖) := f_nn.mono fun _x hx => (abs_of_nonneg hx).symm
  simp_rw [integral_congr_ae this, ofReal_integral_norm_eq_lintegral_enorm hfi,
    ← ofReal_norm]
  exact lintegral_congr_ae (this.symm.fun_comp ENNReal.ofReal)

中文:
定理 of实数_integral_eq_lintegral_of实数
  条件: {f : α -> 实数} (hfi : 可积 f μ) (f_nn : 0 <=ᵐ[μ] f)
  证明: by
  have : f =ᵐ[μ] (‖f ·‖) := f_nn.mono fun _x hx => (abs_of_nonneg hx).symm
  simp_rw [integral_congr_ae this, ofReal_integral_norm_eq_lintegral_enorm hfi,
    ← ofReal_norm]
  exact lintegral_congr_ae (this.symm.fun_comp ENNReal.ofReal)

Depends on / 依赖: ENNReal, ENNReal.ofReal, abs_of_nonneg, f_nn, f_nn.mono, fun_comp, integral_congr_ae, lintegral_congr_ae, ofReal, ofReal_integral_norm_eq_lintegral_enorm, ofReal_norm, simp_rw, this.symm.fun_comp
-/
theorem ofReal_integral_eq_lintegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have : f =ᵐ[μ] (‖f ·‖) := f_nn.mono fun _x hx => (abs_of_nonneg hx).symm
  simp_rw [integral_congr_ae this, ofReal_integral_norm_eq_lintegral_enorm hfi,
    ← ofReal_norm]
  exact lintegral_congr_ae (this.symm.fun_comp ENNReal.ofReal)

/--
theorem `integral_toReal` / 定理 `integral_toReal`

English:
theorem integral_toReal
  given: {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞)
  proof: by
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.ennreal_toReal.aestronglyMeasurable]; rw [lintegral_congr_ae (ofReal_toReal_ae_eq hf)]
  exact Eventually.of_forall fun x => ENNReal.toReal_nonneg

中文:
定理 integral_to实数
  条件: {f : α -> 实数>=0∞} (hfm : 几乎处处可测 f μ) (hf : 对任意ᵐ x ∂μ, f x < ∞)
  证明: by
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.ennreal_toReal.aestronglyMeasurable]; rw [lintegral_congr_ae (ofReal_toReal_ae_eq hf)]
  exact Eventually.of_forall fun x => ENNReal.toReal_nonneg

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Eventually, Eventually.of_forall, aestronglyMeasurable, ennreal_toReal, hfm.ennreal_toReal.aestronglyMeasurable, integral_eq_lintegral_of_nonneg_ae, lintegral_congr_ae, ofReal_toReal_ae_eq, of_forall, toReal_nonneg
-/
theorem integral_toReal {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) :
    ∫ a, (f a).toReal ∂μ = (∫⁻ a, f a ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.ennreal_toReal.aestronglyMeasurable]; rw [lintegral_congr_ae (ofReal_toReal_ae_eq hf)]
  exact Eventually.of_forall fun x => ENNReal.toReal_nonneg

/--
theorem `lintegral_coe_le_coe_iff_integral_le` / 定理 `lintegral_coe_le_coe_iff_integral_le`

English:
theorem lintegral_coe_le_coe_iff_integral_le
  statement: {f : α -> Real>=0} (hfi : Integrable (fun x => (f x : Real)) μ)
  proof: by
  rw [lintegral_coe_eq_integral f hfi]; rw [ENNReal.ofReal]; rw [ENNReal.coe_le_coe]; rw [Real.toNNReal_le_iff_le_coe]

中文:
定理 lintegral_coe_le_coe_iff_integral_le
  结论: {f : α -> 实数>=0} (hfi : 可积 (fun x => (f x : 实数)) μ)
  证明: by
  rw [lintegral_coe_eq_integral f hfi]; rw [ENNReal.ofReal]; rw [ENNReal.coe_le_coe]; rw [Real.toNNReal_le_iff_le_coe]

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.ofReal, Real.toNNReal_le_iff_le_coe, coe_le_coe, lintegral_coe_eq_integral, ofReal, toNNReal_le_iff_le_coe
-/
theorem lintegral_coe_le_coe_iff_integral_le {f : α -> Real>=0} (hfi : Integrable (fun x => (f x : Real)) μ)
    {b : Real>=0} : ∫⁻ a, f a ∂μ <= b ↔ ∫ a, (f a : Real) ∂μ <= b := by
  rw [lintegral_coe_eq_integral f hfi]; rw [ENNReal.ofReal]; rw [ENNReal.coe_le_coe]; rw [Real.toNNReal_le_iff_le_coe]

/--
theorem `integral_coe_le_of_lintegral_coe_le` / 定理 `integral_coe_le_of_lintegral_coe_le`

English:
theorem integral_coe_le_of_lintegral_coe_le
  given: {f : α -> Real>=0} {b : Real>=0} (h : ∫⁻ a, f a ∂μ <= b)
  proof: by
  by_cases hf : Integrable (fun a => (f a : Real)) μ
  · exact (lintegral_coe_le_coe_iff_integral_le hf).1 h
  · rw [integral_undef hf]; exact b.2

中文:
定理 integral_coe_le_of_lintegral_coe_le
  条件: {f : α -> 实数>=0} {b : 实数>=0} (h : ∫⁻ a, f a ∂μ <= b)
  证明: by
  by_cases hf : Integrable (fun a => (f a : Real)) μ
  · exact (lintegral_coe_le_coe_iff_integral_le hf).1 h
  · rw [integral_undef hf]; exact b.2

Depends on / 依赖: Integrable, integral_undef, lintegral_coe_le_coe_iff_integral_le
-/
theorem integral_coe_le_of_lintegral_coe_le {f : α -> Real>=0} {b : Real>=0} (h : ∫⁻ a, f a ∂μ <= b) :
    ∫ a, (f a : Real) ∂μ <= b := by
  by_cases hf : Integrable (fun a => (f a : Real)) μ
  · exact (lintegral_coe_le_coe_iff_integral_le hf).1 h
  · rw [integral_undef hf]; exact b.2

/--
theorem `integral_eq_zero_iff_of_nonneg_ae` / 定理 `integral_eq_zero_iff_of_nonneg_ae`

English:
theorem integral_eq_zero_iff_of_nonneg_ae
  given: {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ)
  proof: by
  simp_rw [integral_eq_lintegral_of_nonneg_ae hf hfi.1, ENNReal.toReal_eq_zero_iff,
    ← ENNReal.not_lt_top, ← hasFiniteIntegral_iff_ofReal hf, hfi.2, not_true_eq_false, or_false]
  rw [lintegral_eq_zero_iff']
  · rw [← hf.ge_iff_eq', Filter.EventuallyEq, Filter.EventuallyLE]
    simp only [Pi.z

中文:
定理 integral_eq_zero_iff_of_nonneg_ae
  条件: {f : α -> 实数} (hf : 0 <=ᵐ[μ] f) (hfi : 可积 f μ)
  证明: by
  simp_rw [integral_eq_lintegral_of_nonneg_ae hf hfi.1, ENNReal.toReal_eq_zero_iff,
    ← ENNReal.not_lt_top, ← hasFiniteIntegral_iff_ofReal hf, hfi.2, not_true_eq_false, or_false]
  rw [lintegral_eq_zero_iff']
  · rw [← hf.ge_iff_eq', Filter.EventuallyEq, Filter.EventuallyLE]
    simp only [Pi.z

Depends on / 依赖: ENNReal, ENNReal.measurable_ofReal.comp_aemeasurable, ENNReal.not_lt_top, ENNReal.toReal_eq_zero_iff, EventuallyEq, EventuallyLE, Filter, Filter.EventuallyEq, Filter.EventuallyLE, Pi.zero_apply, aemeasurable, comp_aemeasurable, ge_iff_eq, hasFiniteIntegral_iff_ofReal, hf.ge_iff_eq, integral_eq_lintegral_of_nonneg_ae, lintegral_eq_zero_iff, measurable_ofReal, not_lt_top, not_true_eq_false
-/
theorem integral_eq_zero_iff_of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae hf hfi.1, ENNReal.toReal_eq_zero_iff,
    ← ENNReal.not_lt_top, ← hasFiniteIntegral_iff_ofReal hf, hfi.2, not_true_eq_false, or_false]
  rw [lintegral_eq_zero_iff']
  · rw [← hf.ge_iff_eq', Filter.EventuallyEq, Filter.EventuallyLE]
    simp only [Pi.zero_apply, ofReal_eq_zero]
  · exact (ENNReal.measurable_ofReal.comp_aemeasurable hfi.1.aemeasurable)

/--
theorem `integral_eq_zero_iff_of_nonneg` / 定理 `integral_eq_zero_iff_of_nonneg`

English:
theorem integral_eq_zero_iff_of_nonneg
  given: {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ)
  proof: integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf) hfi

中文:
定理 integral_eq_zero_iff_of_nonneg
  条件: {f : α -> 实数} (hf : 0 <= f) (hfi : 可积 f μ)
  证明: integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf) hfi

Depends on / 依赖: Eventually, Eventually.of_forall, integral_eq_zero_iff_of_nonneg_ae, of_forall
-/
theorem integral_eq_zero_iff_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf) hfi

/--
lemma `integral_eq_iff_of_ae_le` / 引理 `integral_eq_iff_of_ae_le`

English:
lemma integral_eq_iff_of_ae_le
  statement: {f g : α -> Real}
  proof: by
  refine ⟨fun h_le => EventuallyEq.symm ?_, fun h => integral_congr_ae h⟩
  rw [← sub_ae_eq_zero]; rw [← integral_eq_zero_iff_of_nonneg_ae ((sub_nonneg_ae _ _).mpr hfg) (hg.sub hf)]
  simpa [Pi.sub_apply, integral_sub hg hf, sub_eq_zero, eq_comm]

中文:
引理 integral_eq_iff_of_ae_le
  结论: {f g : α -> 实数}
  证明: by
  refine ⟨fun h_le => EventuallyEq.symm ?_, fun h => integral_congr_ae h⟩
  rw [← sub_ae_eq_zero]; rw [← integral_eq_zero_iff_of_nonneg_ae ((sub_nonneg_ae _ _).mpr hfg) (hg.sub hf)]
  simpa [Pi.sub_apply, integral_sub hg hf, sub_eq_zero, eq_comm]

Depends on / 依赖: EventuallyEq, EventuallyEq.symm, Pi.sub_apply, eq_comm, h_le, hg.sub, integral_congr_ae, integral_eq_zero_iff_of_nonneg_ae, integral_sub, sub_ae_eq_zero, sub_apply, sub_eq_zero, sub_nonneg_ae
-/
lemma integral_eq_iff_of_ae_le {f g : α -> Real}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f <=ᵐ[μ] g) :
    ∫ a, f a ∂μ = ∫ a, g a ∂μ ↔ f =ᵐ[μ] g := by
  refine ⟨fun h_le => EventuallyEq.symm ?_, fun h => integral_congr_ae h⟩
  rw [← sub_ae_eq_zero]; rw [← integral_eq_zero_iff_of_nonneg_ae ((sub_nonneg_ae _ _).mpr hfg) (hg.sub hf)]
  simpa [Pi.sub_apply, integral_sub hg hf, sub_eq_zero, eq_comm]

/--
theorem `integral_pos_iff_support_of_nonneg_ae` / 定理 `integral_pos_iff_support_of_nonneg_ae`

English:
theorem integral_pos_iff_support_of_nonneg_ae
  given: {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ)
  proof: by
  simp_rw [(integral_nonneg_of_ae hf).lt_iff_ne, pos_iff_ne_zero, Ne, @eq_comm Real 0,
    integral_eq_zero_iff_of_nonneg_ae hf hfi, Filter.EventuallyEq, ae_iff, Pi.zero_apply,
    Function.support]

中文:
定理 integral_pos_iff_support_of_nonneg_ae
  条件: {f : α -> 实数} (hf : 0 <=ᵐ[μ] f) (hfi : 可积 f μ)
  证明: by
  simp_rw [(integral_nonneg_of_ae hf).lt_iff_ne, pos_iff_ne_zero, Ne, @eq_comm Real 0,
    integral_eq_zero_iff_of_nonneg_ae hf hfi, Filter.EventuallyEq, ae_iff, Pi.zero_apply,
    Function.support]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Function, Function.support, Pi.zero_apply, ae_iff, eq_comm, integral_eq_zero_iff_of_nonneg_ae, integral_nonneg_of_ae, lt_iff_ne, pos_iff_ne_zero, simp_rw, support, zero_apply
-/
theorem integral_pos_iff_support_of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) :
    (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f) := by
  simp_rw [(integral_nonneg_of_ae hf).lt_iff_ne, pos_iff_ne_zero, Ne, @eq_comm Real 0,
    integral_eq_zero_iff_of_nonneg_ae hf hfi, Filter.EventuallyEq, ae_iff, Pi.zero_apply,
    Function.support]

/--
theorem `integral_pos_iff_support_of_nonneg` / 定理 `integral_pos_iff_support_of_nonneg`

English:
theorem integral_pos_iff_support_of_nonneg
  given: {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ)
  proof: integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hf) hfi

中文:
定理 integral_pos_iff_support_of_nonneg
  条件: {f : α -> 实数} (hf : 0 <= f) (hfi : 可积 f μ)
  证明: integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hf) hfi

Depends on / 依赖: Eventually, Eventually.of_forall, integral_pos_iff_support_of_nonneg_ae, of_forall
-/
theorem integral_pos_iff_support_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ) :
    (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f) :=
  integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hf) hfi

/--
lemma `integral_exp_pos` / 引理 `integral_exp_pos`

English:
lemma integral_exp_pos
  statement: {μ : Measure α} {f : α -> Real} [hμ : NeZero μ]
  proof: by
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hf]
  suffices (Function.support fun x => Real.exp (f x)) = Set.univ by simp [this, hμ.out]
  ext1 x
  simp only [Function.mem_support, ne_eq, (Real.exp_pos _).ne', not_false_eq_true, Set.mem_univ]

中文:
引理 integral_exp_pos
  结论: {μ : 测度 α} {f : α -> 实数} [hμ : NeZero μ]
  证明: by
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hf]
  suffices (Function.support fun x => Real.exp (f x)) = Set.univ by simp [this, hμ.out]
  ext1 x
  simp only [Function.mem_support, ne_eq, (Real.exp_pos _).ne', not_false_eq_true, Set.mem_univ]

Depends on / 依赖: Function, Function.mem_support, Function.support, Real.exp, Real.exp_pos, Set.mem_univ, Set.univ, exp_pos, integral_pos_iff_support_of_nonneg, mem_support, mem_univ, ne_eq, not_false_eq_true, support
-/
lemma integral_exp_pos {μ : Measure α} {f : α -> Real} [hμ : NeZero μ]
    (hf : Integrable (fun x => Real.exp (f x)) μ) :
    0 < ∫ x, Real.exp (f x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hf]
  suffices (Function.support fun x => Real.exp (f x)) = Set.univ by simp [this, hμ.out]
  ext1 x
  simp only [Function.mem_support, ne_eq, (Real.exp_pos _).ne', not_false_eq_true, Set.mem_univ]

/--
lemma `integral_tendsto_of_tendsto_of_monotone` / 引理 `integral_tendsto_of_tendsto_of_monotone`

English:
lemma integral_tendsto_of_tendsto_of_monotone
  statement: {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real}
  proof: by
  -- switch from the Bochner to the Lebesgue integral
  let f' := fun n x => f n x - f 0 x
  have hf'_nonneg : forallᵐ x ∂μ, forall n, 0 <= f' n x := by
    filter_upwards [h_mono] with a ha n
    simp [f', ha zero_le]
  have hf'_meas : forall n, Integrable (f' n) μ := fun n => (hf n).sub (hf 0)


中文:
引理 integral_tendsto_of_tendsto_of_monotone
  结论: {μ : 测度 α} {f : 自然数 -> α -> 实数} {F : α -> 实数}
  证明: by
  -- switch from the Bochner to the Lebesgue integral
  let f' := fun n x => f n x - f 0 x
  have hf'_nonneg : forallᵐ x ∂μ, forall n, 0 <= f' n x := by
    filter_upwards [h_mono] with a ha n
    simp [f', ha zero_le]
  have hf'_meas : forall n, Integrable (f' n) μ := fun n => (hf n).sub (hf 0)

-/
lemma integral_tendsto_of_tendsto_of_monotone {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real}
    (hf : forall n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : forallᵐ x ∂μ, Monotone fun n => f n x)
    (h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  -- switch from the Bochner to the Lebesgue integral
  let f' := fun n x => f n x - f 0 x
  have hf'_nonneg : forallᵐ x ∂μ, forall n, 0 <= f' n x := by
    filter_upwards [h_mono] with a ha n
    simp [f', ha zero_le]
  have hf'_meas : forall n, Integrable (f' n) μ := fun n => (hf n).sub (hf 0)
  suffices Tendsto (fun n => ∫ x, f' n x ∂μ) atTop (𝓝 (∫ x, (F - f 0) x ∂μ)) by
    simp_rw [f', integral_sub (hf _) (hf _), integral_sub' hF (hf 0),
      tendsto_sub_const_iff] at this
    exact this
  have hF_ge : 0 <=ᵐ[μ] fun x => (F - f 0) x := by
    filter_upwards [h_tendsto, h_mono] with x hx_tendsto hx_mono
    simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    exact ge_of_tendsto' hx_tendsto (fun n => hx_mono zero_le)
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
  · exact fun n => ((hf n).sub (hf 0)).aemeasurable.ennreal_ofReal
  · filter_upwards [h_mono] with x hx n m hnm
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [f', tsub_le_iff_right, sub_add_cancel]
    exact hx hnm
  · filter_upwards [h_tendsto] with x hx
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simp only [Pi.sub_apply]
    exact Tendsto.sub hx tendsto_const_nhds

/--
lemma `integral_tendsto_of_tendsto_of_antitone` / 引理 `integral_tendsto_of_tendsto_of_antitone`

English:
lemma integral_tendsto_of_tendsto_of_antitone
  statement: {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real}
  proof: by
  suffices Tendsto (fun n => ∫ x, -f n x ∂μ) atTop (𝓝 (∫ x, -F x ∂μ)) by
    suffices Tendsto (fun n => ∫ x, - -f n x ∂μ) atTop (𝓝 (∫ x, - -F x ∂μ)) by
      simpa [neg_neg] using this
    convert! this.neg <;> rw [integral_neg]
  refine integral_tendsto_of_tendsto_of_monotone (fun n => (hf n).ne

中文:
引理 integral_tendsto_of_tendsto_of_antitone
  结论: {μ : 测度 α} {f : 自然数 -> α -> 实数} {F : α -> 实数}
  证明: by
  suffices Tendsto (fun n => ∫ x, -f n x ∂μ) atTop (𝓝 (∫ x, -F x ∂μ)) by
    suffices Tendsto (fun n => ∫ x, - -f n x ∂μ) atTop (𝓝 (∫ x, - -F x ∂μ)) by
      simpa [neg_neg] using this
    convert! this.neg <;> rw [integral_neg]
  refine integral_tendsto_of_tendsto_of_monotone (fun n => (hf n).ne

Depends on / 依赖: Tendsto, convert, filter_upwards, hF.neg, h_mono, h_tendsto, hx.neg, integral_neg, integral_tendsto_of_tendsto_of_monotone, neg_le_neg_iff, neg_le_neg_iff.mpr, neg_neg, this.neg
-/
lemma integral_tendsto_of_tendsto_of_antitone {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real}
    (hf : forall n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : forallᵐ x ∂μ, Antitone fun n => f n x)
    (h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  suffices Tendsto (fun n => ∫ x, -f n x ∂μ) atTop (𝓝 (∫ x, -F x ∂μ)) by
    suffices Tendsto (fun n => ∫ x, - -f n x ∂μ) atTop (𝓝 (∫ x, - -F x ∂μ)) by
      simpa [neg_neg] using this
    convert! this.neg <;> rw [integral_neg]
  refine integral_tendsto_of_tendsto_of_monotone (fun n => (hf n).neg) hF.neg ?_ ?_
· filter_upwards [h_mono] with x hx n m hnm using neg_le_neg_iff.mpr hx hnm
  · filter_upwards [h_tendsto] with x hx using hx.neg

/--
lemma `tendsto_of_integral_tendsto_of_monotone` / 引理 `tendsto_of_integral_tendsto_of_monotone`

English:
lemma tendsto_of_integral_tendsto_of_monotone
  statement: {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real}
  proof: by
  -- reduce to the `ℝ≥0∞` case
  let f' : Nat -> α -> Real>=0∞ := fun n a => ENNReal.ofReal (f n a - f 0 a)
  let F' : α -> Real>=0∞ := fun a => ENNReal.ofReal (F a - f 0 a)
  have hf'_int_eq : forall i, ∫⁻ a, f' i a ∂μ = ENNReal.ofReal (∫ a, f i a ∂μ - ∫ a, f 0 a ∂μ) := by
    intro i
    unfold

中文:
引理 tendsto_of_integral_tendsto_of_monotone
  结论: {μ : 测度 α} {f : 自然数 -> α -> 实数} {F : α -> 实数}
  证明: by
  -- reduce to the `ℝ≥0∞` case
  let f' : Nat -> α -> Real>=0∞ := fun n a => ENNReal.ofReal (f n a - f 0 a)
  let F' : α -> Real>=0∞ := fun a => ENNReal.ofReal (F a - f 0 a)
  have hf'_int_eq : forall i, ∫⁻ a, f' i a ∂μ = ENNReal.ofReal (∫ a, f i a ∂μ - ∫ a, f 0 a ∂μ) := by
    intro i
    unfold
-/
lemma tendsto_of_integral_tendsto_of_monotone {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real}
    (hf_int : forall n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i => ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)))
    (hf_mono : forallᵐ a ∂μ, Monotone (fun i => f i a))
    (hf_bound : forallᵐ a ∂μ, forall i, f i a <= F a) :
    forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F a)) := by
  -- reduce to the `ℝ≥0∞` case
  let f' : Nat -> α -> Real>=0∞ := fun n a => ENNReal.ofReal (f n a - f 0 a)
  let F' : α -> Real>=0∞ := fun a => ENNReal.ofReal (F a - f 0 a)
  have hf'_int_eq : forall i, ∫⁻ a, f' i a ∂μ = ENNReal.ofReal (∫ a, f i a ∂μ - ∫ a, f 0 a ∂μ) := by
    intro i
    unfold f'
    rw [← ofReal_integral_eq_lintegral_ofReal]; rw [integral_sub (hf_int i) (hf_int 0)]
    · exact (hf_int i).sub (hf_int 0)
    · filter_upwards [hf_mono] with a h_mono
      simp [h_mono zero_le]
  have hF'_int_eq : ∫⁻ a, F' a ∂μ = ENNReal.ofReal (∫ a, F a ∂μ - ∫ a, f 0 a ∂μ) := by
    unfold F'
    rw [← ofReal_integral_eq_lintegral_ofReal]; rw [integral_sub hF_int (hf_int 0)]
    · exact hF_int.sub (hf_int 0)
    · filter_upwards [hf_bound] with a h_bound
      simp [h_bound 0]
  have h_tendsto : Tendsto (fun i => ∫⁻ a, f' i a ∂μ) atTop (𝓝 (∫⁻ a, F' a ∂μ)) := by
    simp_rw [hf'_int_eq, hF'_int_eq]
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    rwa [tendsto_sub_const_iff]
  have h_mono : forallᵐ a ∂μ, Monotone (fun i => f' i a) := by
    filter_upwards [hf_mono] with a ha_mono i j hij
    refine ENNReal.ofReal_le_ofReal ?_
    simp [ha_mono hij]
  have h_bound : forallᵐ a ∂μ, forall i, f' i a <= F' a := by
    filter_upwards [hf_bound] with a ha_bound i
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [tsub_le_iff_right, sub_add_cancel, ha_bound i]
  -- use the corresponding lemma for `ℝ≥0∞`
  have h := tendsto_of_lintegral_tendsto_of_monotone ?_ h_tendsto h_mono h_bound ?_
  rotate_left
  · exact (hF_int.1.aemeasurable.sub (hf_int 0).1.aemeasurable).ennreal_ofReal
  · exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt (hF_int.sub (hf_int 0)).2).ne
  filter_upwards [h, hf_mono, hf_bound] with a ha ha_mono ha_bound
  have h1 : (fun i => f i a) = fun i => (f' i a).toReal + f 0 a := by
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
  rw [h1]; rw [h2]
  refine Filter.Tendsto.add ?_ tendsto_const_nhds
  exact (ENNReal.continuousAt_toReal (by finiteness)).tendsto.comp ha

/--
lemma `tendsto_of_integral_tendsto_of_antitone` / 引理 `tendsto_of_integral_tendsto_of_antitone`

English:
lemma tendsto_of_integral_tendsto_of_antitone
  statement: {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real}
  proof: by
  let f' : Nat -> α -> Real := fun i a => - f i a
  let F' : α -> Real := fun a => - F a
  suffices forallᵐ a ∂μ, Tendsto (fun i => f' i a) atTop (𝓝 (F' a)) by
    filter_upwards [this] with a ha_tendsto
    convert! ha_tendsto.neg
    · simp [f']
    · simp [F']
  refine tendsto_of_integral_tend

中文:
引理 tendsto_of_integral_tendsto_of_antitone
  结论: {μ : 测度 α} {f : 自然数 -> α -> 实数} {F : α -> 实数}
  证明: by
  let f' : Nat -> α -> Real := fun i a => - f i a
  let F' : α -> Real := fun a => - F a
  suffices forallᵐ a ∂μ, Tendsto (fun i => f' i a) atTop (𝓝 (F' a)) by
    filter_upwards [this] with a ha_tendsto
    convert! ha_tendsto.neg
    · simp [f']
    · simp [F']
  refine tendsto_of_integral_tend

Depends on / 依赖: Tendsto, convert, filter_upwards, hF_int, hF_int.neg, ha_tendsto, ha_tendsto.neg, hf_bound, hf_int, hf_mono, hf_tendsto, hf_tendsto.neg, integral_neg, tendsto_of_integral_tendsto_of_monotone
-/
lemma tendsto_of_integral_tendsto_of_antitone {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real}
    (hf_int : forall n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i => ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)))
    (hf_mono : forallᵐ a ∂μ, Antitone (fun i => f i a))
    (hf_bound : forallᵐ a ∂μ, forall i, F a <= f i a) :
    forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F a)) := by
  let f' : Nat -> α -> Real := fun i a => - f i a
  let F' : α -> Real := fun a => - F a
  suffices forallᵐ a ∂μ, Tendsto (fun i => f' i a) atTop (𝓝 (F' a)) by
    filter_upwards [this] with a ha_tendsto
    convert! ha_tendsto.neg
    · simp [f']
    · simp [F']
  refine tendsto_of_integral_tendsto_of_monotone (fun n => (hf_int n).neg) hF_int.neg ?_ ?_ ?_
  · convert! hf_tendsto.neg
    · rw [integral_neg]
    · rw [integral_neg]
  · filter_upwards [hf_mono] with a ha i j hij
    simp [f', ha hij]
  · filter_upwards [hf_bound] with a ha i
    simp [f', F', ha i]

section NormedAddCommGroup

variable {H : Type*} [NormedAddCommGroup H]

/--
theorem `L1.norm_eq_integral_norm` / 定理 `L1.norm_eq_integral_norm`

English:
theorem L1.norm_eq_integral_norm
  given: (f : α ->₁[μ] H)
  statement: ‖f‖ = ∫ a, ‖f a‖ ∂μ
  proof: by
  simp only [eLpNorm, eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_one, ENNReal.rpow_one,
    Lp.norm_def, if_false, ENNReal.one_ne_top, one_ne_zero, _root_.div_one]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (by simp [norm_nonneg]))
      (Lp.aestronglyMeasurable f).norm]
  si

中文:
定理 L1.norm_eq_integral_norm
  条件: (f : α ->₁[μ] H)
  结论: ‖f‖ = ∫ a, ‖f a‖ ∂μ
  证明: by
  simp only [eLpNorm, eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_one, ENNReal.rpow_one,
    Lp.norm_def, if_false, ENNReal.one_ne_top, one_ne_zero, _root_.div_one]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (by simp [norm_nonneg]))
      (Lp.aestronglyMeasurable f).norm]
  si

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, ENNReal.rpow_one, ENNReal.toReal_one, Eventually, Eventually.of_forall, Lp.aestronglyMeasurable, Lp.norm_def, _eq_lintegral_enorm, _root_, _root_.div_one, aestronglyMeasurable, div_one, eLpNorm, if_false, integral_eq_lintegral_of_nonneg_ae, norm_def, norm_nonneg, of_forall, one_ne_top
-/
theorem L1.norm_eq_integral_norm (f : α ->₁[μ] H) : ‖f‖ = ∫ a, ‖f a‖ ∂μ := by
  simp only [eLpNorm, eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_one, ENNReal.rpow_one,
    Lp.norm_def, if_false, ENNReal.one_ne_top, one_ne_zero, _root_.div_one]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (by simp [norm_nonneg]))
      (Lp.aestronglyMeasurable f).norm]
  simp

/--
theorem `L1.dist_eq_integral_dist` / 定理 `L1.dist_eq_integral_dist`

English:
theorem L1.dist_eq_integral_dist
  given: (f g : α ->₁[μ] H)
  statement: dist f g = ∫ a, dist (f a) (g a) ∂μ
  proof: by
  simp only [dist_eq_norm, L1.norm_eq_integral_norm]
exact integral_congr_ae (Lp.coeFn_sub _ _).fun_comp norm

中文:
定理 L1.dist_eq_integral_dist
  条件: (f g : α ->₁[μ] H)
  结论: dist f g = ∫ a, dist (f a) (g a) ∂μ
  证明: by
  simp only [dist_eq_norm, L1.norm_eq_integral_norm]
exact integral_congr_ae (Lp.coeFn_sub _ _).fun_comp norm

Depends on / 依赖: L1.norm_eq_integral_norm, Lp.coeFn_sub, coeFn_sub, dist_eq_norm, fun_comp, integral_congr_ae, norm_eq_integral_norm
-/
theorem L1.dist_eq_integral_dist (f g : α ->₁[μ] H) : dist f g = ∫ a, dist (f a) (g a) ∂μ := by
  simp only [dist_eq_norm, L1.norm_eq_integral_norm]
exact integral_congr_ae (Lp.coeFn_sub _ _).fun_comp norm

/--
theorem `L1.norm_of_fun_eq_integral_norm` / 定理 `L1.norm_of_fun_eq_integral_norm`

English:
theorem L1.norm_of_fun_eq_integral_norm
  given: {f : α -> H} (hf : Integrable f μ)
  proof: by
  rw [L1.norm_eq_integral_norm]
exact integral_congr_ae hf.coeFn_toL1.fun_comp _

中文:
定理 L1.norm_of_fun_eq_integral_norm
  条件: {f : α -> H} (hf : 可积 f μ)
  证明: by
  rw [L1.norm_eq_integral_norm]
exact integral_congr_ae hf.coeFn_toL1.fun_comp _

Depends on / 依赖: L1.norm_eq_integral_norm, coeFn_toL1, fun_comp, hf.coeFn_toL1.fun_comp, integral_congr_ae, norm_eq_integral_norm
-/
theorem L1.norm_of_fun_eq_integral_norm {f : α -> H} (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ∫ a, ‖f a‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
exact integral_congr_ae hf.coeFn_toL1.fun_comp _

/--
theorem `MemLp.eLpNorm_eq_integral_rpow_norm` / 定理 `MemLp.eLpNorm_eq_integral_rpow_norm`

English:
theorem MemLp.eLpNorm_eq_integral_rpow_norm
  statement: {f : α -> H} {p : Real>=0∞} (hp1 : p != 0) (hp2 : p != ∞)
  proof: by
  have A : ∫⁻ a : α, ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ = ∫⁻ a : α, ‖f a‖ₑ ^ p.toReal ∂μ := by
    simp_rw [← ofReal_rpow_of_nonneg (norm_nonneg _) toReal_nonneg, ofReal_norm]
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 hp2, one_div]
  rw [integral_eq_lintegral_of_nonneg_ae]; rotate

中文:
定理 MemLp.eLpNorm_eq_integral_rpow_norm
  结论: {f : α -> H} {p : 实数>=0∞} (hp1 : p != 0) (hp2 : p != ∞)
  证明: by
  have A : ∫⁻ a : α, ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ = ∫⁻ a : α, ‖f a‖ₑ ^ p.toReal ∂μ := by
    simp_rw [← ofReal_rpow_of_nonneg (norm_nonneg _) toReal_nonneg, ofReal_norm]
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 hp2, one_div]
  rw [integral_eq_lintegral_of_nonneg_ae]; rotate

Depends on / 依赖: ENNReal, ENNReal.ofReal, ae_of_all, aemeasurable, aestronglyMeasurable, eLpNorm_eq_lintegral_rpow_enorm_toReal, hf.aestronglyMeasurable.norm.aemeasurable.pow_const, integral_eq_lintegral_of_nonneg_ae, inv_nonneg, norm_nonneg, ofReal, ofReal_norm, ofReal_rpow_of_nonneg, one_div, p.toReal, pow_const, rotate_left, simp_rw, toReal, toReal_nonne
-/
theorem MemLp.eLpNorm_eq_integral_rpow_norm {f : α -> H} {p : Real>=0∞} (hp1 : p != 0) (hp2 : p != ∞)
    (hf : MemLp f p μ) :
    eLpNorm f p μ = ENNReal.ofReal ((∫ a, ‖f a‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) := by
  have A : ∫⁻ a : α, ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ = ∫⁻ a : α, ‖f a‖ₑ ^ p.toReal ∂μ := by
    simp_rw [← ofReal_rpow_of_nonneg (norm_nonneg _) toReal_nonneg, ofReal_norm]
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 hp2, one_div]
  rw [integral_eq_lintegral_of_nonneg_ae]; rotate_left
  · exact ae_of_all _ fun x => by positivity
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [A]; rw [← ofReal_rpow_of_nonneg toReal_nonneg (inv_nonneg.2 toReal_nonneg)]; rw [ofReal_toReal]
  exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp1 hp2 hf.2).ne

end NormedAddCommGroup

/--
theorem `norm_integral_le_integral_norm` / 定理 `norm_integral_le_integral_norm`

English:
theorem norm_integral_le_integral_norm
  given: (f : α -> G)
  statement: ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
  proof: by
  have le_ae : forallᵐ a ∂μ, 0 <= ‖f a‖ := Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ
  · calc
      ‖∫ a, f a ∂μ‖ <= ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) :=
        norm_integral_le_lintegral_norm _
      _ = ∫ a, ‖f a‖ ∂μ := (integral_eq_linteg

中文:
定理 norm_integral_le_integral_norm
  条件: (f : α -> G)
  结论: ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
  证明: by
  have le_ae : forallᵐ a ∂μ, 0 <= ‖f a‖ := Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ
  · calc
      ‖∫ a, f a ∂μ‖ <= ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) :=
        norm_integral_le_lintegral_norm _
      _ = ∫ a, ‖f a‖ ∂μ := (integral_eq_linteg

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.ofReal, ENNReal.toReal, Eventually, Eventually.of_forall, h.norm, integral_eq_lintegral_of_nonneg_ae, integral_non_aestronglyMeasurable, integral_nonneg_of_ae, le_ae, norm_integral_le_lintegral_norm, norm_nonneg, norm_zero, ofReal, of_forall, toReal
-/
theorem norm_integral_le_integral_norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ := by
  have le_ae : forallᵐ a ∂μ, 0 <= ‖f a‖ := Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ
  · calc
      ‖∫ a, f a ∂μ‖ <= ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) :=
        norm_integral_le_lintegral_norm _
      _ = ∫ a, ‖f a‖ ∂μ := (integral_eq_lintegral_of_nonneg_ae le_ae <| h.norm).symm
  · rw [integral_non_aestronglyMeasurable h, norm_zero]
    exact integral_nonneg_of_ae le_ae

/--
lemma `abs_integral_le_integral_abs` / 引理 `abs_integral_le_integral_abs`

English:
lemma abs_integral_le_integral_abs
  given: {f : α -> Real}
  statement: |∫ a, f a ∂μ| <= ∫ a, |f a| ∂μ
  proof: norm_integral_le_integral_norm f

中文:
引理 abs_integral_le_integral_abs
  条件: {f : α -> 实数}
  结论: |∫ a, f a ∂μ| <= ∫ a, |f a| ∂μ
  证明: norm_integral_le_integral_norm f

Depends on / 依赖: norm_integral_le_integral_norm
-/
lemma abs_integral_le_integral_abs {f : α -> Real} : |∫ a, f a ∂μ| <= ∫ a, |f a| ∂μ :=
  norm_integral_le_integral_norm f

/--
theorem `norm_integral_le_of_norm_le` / 定理 `norm_integral_le_of_norm_le`

English:
theorem norm_integral_le_of_norm_le
  statement: {f : α -> G} {g : α -> Real} (hg : Integrable g μ)
  proof: calc
    ‖∫ x, f x ∂μ‖ <= ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm f
    _ <= ∫ x, g x ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hg h

@[simp]

中文:
定理 norm_integral_le_of_norm_le
  结论: {f : α -> G} {g : α -> 实数} (hg : 可积 g μ)
  证明: calc
    ‖∫ x, f x ∂μ‖ <= ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm f
    _ <= ∫ x, g x ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hg h

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, integral_mono_of_nonneg, norm_integral_le_integral_norm, norm_nonneg, of_forall
-/
theorem norm_integral_le_of_norm_le {f : α -> G} {g : α -> Real} (hg : Integrable g μ)
    (h : forallᵐ x ∂μ, ‖f x‖ <= g x) : ‖∫ x, f x ∂μ‖ <= ∫ x, g x ∂μ :=
  calc
    ‖∫ x, f x ∂μ‖ <= ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm f
    _ <= ∫ x, g x ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hg h

@[simp]
/--
theorem `integral_const` / 定理 `integral_const`

English:
theorem integral_const
  given: (c : E)
  statement: ∫ _ : α, c ∂μ = μ.real univ • c
  proof: by
  by_cases hμ : IsFiniteMeasure μ
  · simp only [integral_eq_setToFun]
    exact setToFun_const (dominatedFinMeasAdditive_weightedSMul _) _
  by_cases hc : c = 0
  · simp [hc, integral_zero]
  · simp [measureReal_def, (integrable_const_iff_isFiniteMeasure hc).not.2 hμ,
      integral_undef, Measu

中文:
定理 integral_const
  条件: (c : E)
  结论: ∫ _ : α, c ∂μ = μ.real univ • c
  证明: by
  by_cases hμ : IsFiniteMeasure μ
  · simp only [integral_eq_setToFun]
    exact setToFun_const (dominatedFinMeasAdditive_weightedSMul _) _
  by_cases hc : c = 0
  · simp [hc, integral_zero]
  · simp [measureReal_def, (integrable_const_iff_isFiniteMeasure hc).not.2 hμ,
      integral_undef, Measu

Depends on / 依赖: IsFiniteMeasure, MeasureTheory, MeasureTheory.not_isFiniteMeasure_iff.mp, dominatedFinMeasAdditive_weightedSMul, integrable_const_iff_isFiniteMeasure, integral_eq_setToFun, integral_undef, integral_zero, measureReal_def, not_isFiniteMeasure_iff, setToFun_const
-/
theorem integral_const (c : E) : ∫ _ : α, c ∂μ = μ.real univ • c := by
  by_cases hμ : IsFiniteMeasure μ
  · simp only [integral_eq_setToFun]
    exact setToFun_const (dominatedFinMeasAdditive_weightedSMul _) _
  by_cases hc : c = 0
  · simp [hc, integral_zero]
  · simp [measureReal_def, (integrable_const_iff_isFiniteMeasure hc).not.2 hμ,
      integral_undef, MeasureTheory.not_isFiniteMeasure_iff.mp hμ]

/--
lemma `integral_eq_const` / 引理 `integral_eq_const`

English:
lemma integral_eq_const
  given: [IsProbabilityMeasure μ] {f : α -> E} {c : E} (hf : forallᵐ x ∂μ, f x = c)
  proof: by simp [integral_congr_ae hf]

中文:
引理 integral_eq_const
  条件: [是概率测度 μ] {f : α -> E} {c : E} (hf : 对任意ᵐ x ∂μ, f x = c)
  证明: by simp [integral_congr_ae hf]

Depends on / 依赖: integral_congr_ae
-/
lemma integral_eq_const [IsProbabilityMeasure μ] {f : α -> E} {c : E} (hf : forallᵐ x ∂μ, f x = c) :
    ∫ x, f x ∂μ = c := by simp [integral_congr_ae hf]

/--
theorem `norm_integral_le_of_norm_le_const` / 定理 `norm_integral_le_of_norm_le_const`

English:
theorem norm_integral_le_of_norm_le_const
  statement: [IsFiniteMeasure μ] {f : α -> G} {C : Real}
  proof: calc
    ‖∫ x, f x ∂μ‖ <= ∫ _, C ∂μ := norm_integral_le_of_norm_le (integrable_const C) h
    _ = C * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

中文:
定理 norm_integral_le_of_norm_le_const
  结论: [是有限测度 μ] {f : α -> G} {C : 实数}
  证明: calc
    ‖∫ x, f x ∂μ‖ <= ∫ _, C ∂μ := norm_integral_le_of_norm_le (integrable_const C) h
    _ = C * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

Depends on / 依赖: integrable_const, integral_const, mul_comm, norm_integral_le_of_norm_le, smul_eq_mul
-/
theorem norm_integral_le_of_norm_le_const [IsFiniteMeasure μ] {f : α -> G} {C : Real}
    (h : forallᵐ x ∂μ, ‖f x‖ <= C) : ‖∫ x, f x ∂μ‖ <= C * μ.real univ :=
  calc
    ‖∫ x, f x ∂μ‖ <= ∫ _, C ∂μ := norm_integral_le_of_norm_le (integrable_const C) h
    _ = C * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

variable {ν : Measure α}

/--
theorem `integral_add_measure` / 定理 `integral_add_measure`

English:
theorem integral_add_measure
  given: {f : α -> G} (hμ : Integrable f μ) (hν : Integrable f ν)
  proof: by
  simp only [integral_eq_setToFun]
  apply setToFun_add_left'' (fun s hs h's => ?_) hμ hν le_rfl zero_le_one zero_le_one zero_le_one
  simp only [Measure.coe_add, Pi.add_apply, add_lt_top] at h's
  simp [weightedSMul, Measure.real, toReal_add, h's.1.ne, h's.2.ne, add_smul]

@[simp]

中文:
定理 integral_add_measure
  条件: {f : α -> G} (hμ : 可积 f μ) (hν : 可积 f ν)
  证明: by
  simp only [integral_eq_setToFun]
  apply setToFun_add_left'' (fun s hs h's => ?_) hμ hν le_rfl zero_le_one zero_le_one zero_le_one
  simp only [Measure.coe_add, Pi.add_apply, add_lt_top] at h's
  simp [weightedSMul, Measure.real, toReal_add, h's.1.ne, h's.2.ne, add_smul]

@[simp]

Depends on / 依赖: Measure, Measure.coe_add, Measure.real, Pi.add_apply, add_apply, add_lt_top, add_smul, coe_add, integral_eq_setToFun, le_rfl, setToFun_add_left, toReal_add, weightedSMul, zero_le_one
-/
theorem integral_add_measure {f : α -> G} (hμ : Integrable f μ) (hν : Integrable f ν) :
    ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν := by
  simp only [integral_eq_setToFun]
  apply setToFun_add_left'' (fun s hs h's => ?_) hμ hν le_rfl zero_le_one zero_le_one zero_le_one
  simp only [Measure.coe_add, Pi.add_apply, add_lt_top] at h's
  simp [weightedSMul, Measure.real, toReal_add, h's.1.ne, h's.2.ne, add_smul]

@[simp]
/--
theorem `integral_zero_measure` / 定理 `integral_zero_measure`

English:
theorem integral_zero_measure
  given: {m : MeasurableSpace α} (f : α -> G)
  proof: by
  simp only [integral_eq_setToFun]
  exact setToFun_measure_zero (dominatedFinMeasAdditive_weightedSMul _) rfl

@[simp]

中文:
定理 integral_zero_measure
  条件: {m : 可测空间 α} (f : α -> G)
  证明: by
  simp only [integral_eq_setToFun]
  exact setToFun_measure_zero (dominatedFinMeasAdditive_weightedSMul _) rfl

@[simp]

Depends on / 依赖: dominatedFinMeasAdditive_weightedSMul, integral_eq_setToFun, setToFun_measure_zero
-/
theorem integral_zero_measure {m : MeasurableSpace α} (f : α -> G) :
    (∫ x, f x ∂(0 : Measure α)) = 0 := by
  simp only [integral_eq_setToFun]
  exact setToFun_measure_zero (dominatedFinMeasAdditive_weightedSMul _) rfl

@[simp]
/--
theorem `setIntegral_measure_zero` / 定理 `setIntegral_measure_zero`

English:
theorem setIntegral_measure_zero
  given: (f : α -> G) {μ : Measure α} {s : Set α} (hs : μ s = 0)
  proof: Measure.restrict_eq_zero.mpr hs ▸ integral_zero_measure f

中文:
定理 set整数egral_measure_zero
  条件: (f : α -> G) {μ : 测度 α} {s : 集合 α} (hs : μ s = 0)
  证明: Measure.restrict_eq_zero.mpr hs ▸ integral_zero_measure f

Depends on / 依赖: Measure, Measure.restrict_eq_zero.mpr, integral_zero_measure, restrict_eq_zero
-/
theorem setIntegral_measure_zero (f : α -> G) {μ : Measure α} {s : Set α} (hs : μ s = 0) :
    ∫ x in s, f x ∂μ = 0 := Measure.restrict_eq_zero.mpr hs ▸ integral_zero_measure f

/--
lemma `integral_of_isEmpty` / 引理 `integral_of_isEmpty`

English:
lemma integral_of_isEmpty
  given: [IsEmpty α] {f : α -> G}
  statement: ∫ x, f x ∂μ = 0
  proof: μ.eq_zero_of_isEmpty ▸ integral_zero_measure _

中文:
引理 integral_of_isEmpty
  条件: [是空 α] {f : α -> G}
  结论: ∫ x, f x ∂μ = 0
  证明: μ.eq_zero_of_isEmpty ▸ integral_zero_measure _

Depends on / 依赖: eq_zero_of_isEmpty, integral_zero_measure
-/
lemma integral_of_isEmpty [IsEmpty α] {f : α -> G} : ∫ x, f x ∂μ = 0 :=
  μ.eq_zero_of_isEmpty ▸ integral_zero_measure _

/--
theorem `integral_finsetSum_measure` / 定理 `integral_finsetSum_measure`

English:
theorem integral_finsetSum_measure
  statement: {ι} {m : MeasurableSpace α} {f : α -> G} {μ : ι -> Measure α}
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ h ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons]; rw [Finset.sum_cons]; rw [← ih hf.2]
    exact integral_add_measure hf.1 (integrable_finsetSum_measure.2 hf.2)

@[deprecated (since := "2026-04-

中文:
定理 integral_finsetSum_measure
  结论: {ι} {m : 可测空间 α} {f : α -> G} {μ : ι -> 测度 α}
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ h ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons]; rw [Finset.sum_cons]; rw [← ih hf.2]
    exact integral_add_measure hf.1 (integrable_finsetSum_measure.2 hf.2)

@[deprecated (since := "2026-04-

Depends on / 依赖: Finset, Finset.cons_induction_on, Finset.forall_mem_cons, Finset.sum_cons, cons_induction_on, forall_mem_cons, integrable_finsetSum_measure, integral_add_measure, sum_cons
-/
theorem integral_finsetSum_measure {ι} {m : MeasurableSpace α} {f : α -> G} {μ : ι -> Measure α}
    {s : Finset ι} (hf : forall i in s, Integrable f (μ i)) :
    ∫ a, f a ∂(∑ i in s, μ i) = ∑ i in s, ∫ a, f a ∂μ i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ h ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons]; rw [Finset.sum_cons]; rw [← ih hf.2]
    exact integral_add_measure hf.1 (integrable_finsetSum_measure.2 hf.2)

@[deprecated (since := "2026-04-08")]
alias integral_finset_sum_measure := integral_finsetSum_measure

/--
theorem `nndist_integral_add_measure_le_lintegral` / 定理 `nndist_integral_add_measure_le_lintegral`

English:
theorem nndist_integral_add_measure_le_lintegral
  proof: by
  rw [integral_add_measure h₁ h₂]; rw [nndist_comm]; rw [nndist_eq_nnnorm]; rw [add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm _

@[simp]

中文:
定理 nndist_integral_add_measure_le_lintegral
  证明: by
  rw [integral_add_measure h₁ h₂]; rw [nndist_comm]; rw [nndist_eq_nnnorm]; rw [add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm _

@[simp]

Depends on / 依赖: add_sub_cancel_left, enorm_integral_le_lintegral_enorm, integral_add_measure, nndist_comm, nndist_eq_nnnorm
-/
theorem nndist_integral_add_measure_le_lintegral
    {f : α -> G} (h₁ : Integrable f μ) (h₂ : Integrable f ν) :
    (nndist (∫ x, f x ∂μ) (∫ x, f x ∂(μ + ν)) : Real>=0∞) <= ∫⁻ x, ‖f x‖ₑ ∂ν := by
  rw [integral_add_measure h₁ h₂]; rw [nndist_comm]; rw [nndist_eq_nnnorm]; rw [add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm _

@[simp]
/--
theorem `integral_smul_measure` / 定理 `integral_smul_measure`

English:
theorem integral_smul_measure
  given: (f : α -> G) (c : Real>=0∞)
  proof: by
  -- First we consider the “degenerate” case `c = ∞`
  rcases eq_or_ne c ∞ with (rfl | hc)
  · rw [ENNReal.toReal_top, zero_smul, integral_eq_setToFun, setToFun_top_smul_measure]
  -- Main case: `c ≠ ∞`
  simp_rw [integral_eq_setToFun, ← setToFun_smul_left]
  have hdfma : DominatedFinMeasAdditive

中文:
定理 integral_smul_measure
  条件: (f : α -> G) (c : 实数>=0∞)
  证明: by
  -- First we consider the “degenerate” case `c = ∞`
  rcases eq_or_ne c ∞ with (rfl | hc)
  · rw [ENNReal.toReal_top, zero_smul, integral_eq_setToFun, setToFun_top_smul_measure]
  -- Main case: `c ≠ ∞`
  simp_rw [integral_eq_setToFun, ← setToFun_smul_left]
  have hdfma : DominatedFinMeasAdditive
-/
theorem integral_smul_measure (f : α -> G) (c : Real>=0∞) :
    ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ := by
  -- First we consider the “degenerate” case `c = ∞`
  rcases eq_or_ne c ∞ with (rfl | hc)
  · rw [ENNReal.toReal_top, zero_smul, integral_eq_setToFun, setToFun_top_smul_measure]
  -- Main case: `c ≠ ∞`
  simp_rw [integral_eq_setToFun, ← setToFun_smul_left]
  have hdfma : DominatedFinMeasAdditive μ (weightedSMul (c • μ) : Set α -> G ->L[Real] G) c.toReal :=
    mul_one c.toReal ▸ (dominatedFinMeasAdditive_weightedSMul (c • μ)).of_smul_measure hc
  have hdfma_smul := dominatedFinMeasAdditive_weightedSMul (F := G) (c • μ)
  rw [← setToFun_congr_smul_measure c hc hdfma hdfma_smul f]
  exact setToFun_congr_left' _ _ (fun s _ _ => weightedSMul_smul_measure μ c) f

@[simp]
/--
theorem `integral_smul_nnreal_measure` / 定理 `integral_smul_nnreal_measure`

English:
theorem integral_smul_nnreal_measure
  given: (f : α -> G) (c : Real>=0)
  proof: integral_smul_measure f (c : Real>=0∞)

中文:
定理 integral_smul_nnreal_measure
  条件: (f : α -> G) (c : 实数>=0)
  证明: integral_smul_measure f (c : Real>=0∞)

Depends on / 依赖: integral_smul_measure
-/
theorem integral_smul_nnreal_measure (f : α -> G) (c : Real>=0) :
    ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ :=
  integral_smul_measure f (c : Real>=0∞)

/--
theorem `integral_map_of_stronglyMeasurable` / 定理 `integral_map_of_stronglyMeasurable`

English:
theorem integral_map_of_stronglyMeasurable
  statement: {β} [MeasurableSpace β] {φ : α -> β} (hφ : Measurable φ)
  proof: by
  by_cases hfi : Integrable f (Measure.map φ μ); swap
  · rw [integral_undef hfi, integral_undef]
    exact fun hfφ => hfi ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hfφ)
  simp only [integral_eq_setToFun]
  apply setToFun_of_le_map_of_stronglyMeasurable _ _
    ((integr

中文:
定理 integral_map_of_stronglyMeasurable
  结论: {β} [可测空间 β] {φ : α -> β} (hφ : 可测 φ)
  证明: by
  by_cases hfi : Integrable f (Measure.map φ μ); swap
  · rw [integral_undef hfi, integral_undef]
    exact fun hfφ => hfi ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hfφ)
  simp only [integral_eq_setToFun]
  apply setToFun_of_le_map_of_stronglyMeasurable _ _
    ((integr

Depends on / 依赖: Integrable, Measure, Measure.map, aemeasurable, aestronglyMeasurable, hfm.aestronglyMeasurable, integrable_map_measure, integral_eq_setToFun, integral_undef, le_rfl, map_measureReal_apply, setToFun_of_le_map_of_stronglyMeasurable, weightedSMul_apply
-/
theorem integral_map_of_stronglyMeasurable {β} [MeasurableSpace β] {φ : α -> β} (hφ : Measurable φ)
    {f : β -> G} (hfm : StronglyMeasurable f) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ := by
  by_cases hfi : Integrable f (Measure.map φ μ); swap
  · rw [integral_undef hfi, integral_undef]
    exact fun hfφ => hfi ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hfφ)
  simp only [integral_eq_setToFun]
  apply setToFun_of_le_map_of_stronglyMeasurable _ _
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).1 hfi) hfm hφ le_rfl
  intro s x hs
  simp [weightedSMul_apply, map_measureReal_apply, hs, hφ]

/--
theorem `integral_map` / 定理 `integral_map`

English:
theorem integral_map
  statement: {β} [MeasurableSpace β] {φ : α -> β} (hφ : AEMeasurable φ μ) {f : β -> G}
  proof: let g := hfm.mk f
  calc
    ∫ y, f y ∂Measure.map φ μ = ∫ y, g y ∂Measure.map φ μ := integral_congr_ae hfm.ae_eq_mk
    _ = ∫ y, g y ∂Measure.map (hφ.mk φ) μ := by congr 1; exact Measure.map_congr hφ.ae_eq_mk
    _ = ∫ x, g (hφ.mk φ x) ∂μ :=
      (integral_map_of_stronglyMeasurable hφ.measurable_m

中文:
定理 integral_map
  结论: {β} [可测空间 β] {φ : α -> β} (hφ : 几乎处处可测 φ μ) {f : β -> G}
  证明: let g := hfm.mk f
  calc
    ∫ y, f y ∂Measure.map φ μ = ∫ y, g y ∂Measure.map φ μ := integral_congr_ae hfm.ae_eq_mk
    _ = ∫ y, g y ∂Measure.map (hφ.mk φ) μ := by congr 1; exact Measure.map_congr hφ.ae_eq_mk
    _ = ∫ x, g (hφ.mk φ x) ∂μ :=
      (integral_map_of_stronglyMeasurable hφ.measurable_m

Depends on / 依赖: Measure, Measure.map, Measure.map_congr, ae_eq_comp, ae_eq_mk, ae_eq_mk.symm.fun_comp, fun_comp, hfm.ae_eq_mk, hfm.ae_eq_mk.symm, hfm.mk, hfm.stronglyMeasurable_mk, integral_congr_ae, integral_map_of_stronglyMeasurable, map_congr, measurable_mk, stronglyMeasurable_mk
-/
theorem integral_map {β} [MeasurableSpace β] {φ : α -> β} (hφ : AEMeasurable φ μ) {f : β -> G}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  let g := hfm.mk f
  calc
    ∫ y, f y ∂Measure.map φ μ = ∫ y, g y ∂Measure.map φ μ := integral_congr_ae hfm.ae_eq_mk
    _ = ∫ y, g y ∂Measure.map (hφ.mk φ) μ := by congr 1; exact Measure.map_congr hφ.ae_eq_mk
    _ = ∫ x, g (hφ.mk φ x) ∂μ :=
      (integral_map_of_stronglyMeasurable hφ.measurable_mk hfm.stronglyMeasurable_mk)
    _ = ∫ x, g (φ x) ∂μ := integral_congr_ae (hφ.ae_eq_mk.symm.fun_comp _)
_ = ∫ x, f (φ x) ∂μ := integral_congr_ae ae_eq_comp hφ hfm.ae_eq_mk.symm

/--
theorem `_root_.MeasurableEmbedding.integral_map` / 定理 `_root_.MeasurableEmbedding.integral_map`

English:
theorem _root_.MeasurableEmbedding.integral_map
  statement: {β} {_ : MeasurableSpace β} {f : α -> β}
  proof: by
  by_cases hgm : AEStronglyMeasurable g (Measure.map f μ)
  · exact MeasureTheory.integral_map hf.measurable.aemeasurable hgm
  · rw [integral_non_aestronglyMeasurable hgm, integral_non_aestronglyMeasurable]
    exact fun hgf => hgm (hf.aestronglyMeasurable_map_iff.2 hgf)

中文:
定理 _root_.可测嵌入.integral_map
  结论: {β} {_ : 可测空间 β} {f : α -> β}
  证明: by
  by_cases hgm : AEStronglyMeasurable g (Measure.map f μ)
  · exact MeasureTheory.integral_map hf.measurable.aemeasurable hgm
  · rw [integral_non_aestronglyMeasurable hgm, integral_non_aestronglyMeasurable]
    exact fun hgf => hgm (hf.aestronglyMeasurable_map_iff.2 hgf)

Depends on / 依赖: AEStronglyMeasurable, Measure, Measure.map, MeasureTheory, MeasureTheory.integral_map, aemeasurable, aestronglyMeasurable_map_iff, hf.aestronglyMeasurable_map_iff, hf.measurable.aemeasurable, integral_map, integral_non_aestronglyMeasurable, measurable
-/
theorem _root_.MeasurableEmbedding.integral_map {β} {_ : MeasurableSpace β} {f : α -> β}
    (hf : MeasurableEmbedding f) (g : β -> G) : ∫ y, g y ∂Measure.map f μ = ∫ x, g (f x) ∂μ := by
  by_cases hgm : AEStronglyMeasurable g (Measure.map f μ)
  · exact MeasureTheory.integral_map hf.measurable.aemeasurable hgm
  · rw [integral_non_aestronglyMeasurable hgm, integral_non_aestronglyMeasurable]
    exact fun hgf => hgm (hf.aestronglyMeasurable_map_iff.2 hgf)

/--
theorem `_root_.Topology.IsClosedEmbedding.integral_map` / 定理 `_root_.Topology.IsClosedEmbedding.integral_map`

English:
theorem _root_.Topology.IsClosedEmbedding.integral_map
  statement: {β} [TopologicalSpace α] [BorelSpace α]
  proof: hφ.measurableEmbedding.integral_map _

中文:
定理 _root_.拓扑.是闭嵌入.integral_map
  结论: {β} [拓扑空间 α] [Borel空间 α]
  证明: hφ.measurableEmbedding.integral_map _

Depends on / 依赖: integral_map, measurableEmbedding, measurableEmbedding.integral_map
-/
theorem _root_.Topology.IsClosedEmbedding.integral_map {β} [TopologicalSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {φ : α -> β} (hφ : IsClosedEmbedding φ)
    (f : β -> G) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  hφ.measurableEmbedding.integral_map _

/--
theorem `integral_map_equiv` / 定理 `integral_map_equiv`

English:
theorem integral_map_equiv
  given: {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β -> G)
  proof: e.measurableEmbedding.integral_map f

omit hE in

中文:
定理 integral_map_equiv
  条件: {β} [可测空间 β] (e : α ≃ᵐ β) (f : β -> G)
  证明: e.measurableEmbedding.integral_map f

omit hE in

Depends on / 依赖: e.measurableEmbedding.integral_map, integral_map, measurableEmbedding
-/
theorem integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β -> G) :
    ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ :=
  e.measurableEmbedding.integral_map f

omit hE in
/--
lemma `integral_domSMul` / 引理 `integral_domSMul`

English:
lemma integral_domSMul
  statement: {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  proof: integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f

中文:
引理 integral_domSMul
  结论: {G A : 类型} [群 G] [加法交换群 A] [分配乘法作用 G A]
  证明: integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f

Depends on / 依赖: DomMulAct, DomMulAct.mk.symm, MeasurableEquiv, MeasurableEquiv.smul, integral_map_equiv
-/
lemma integral_domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [MeasurableSpace A] [MeasurableConstSMul G A] {μ : Measure A} (g : Gᵈᵐᵃ) (f : A -> E) :
    ∫ x, f x ∂g • μ = ∫ x, f ((DomMulAct.mk.symm g)⁻¹ • x) ∂μ :=
  integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f

/--
theorem `MeasurePreserving.integral_comp` / 定理 `MeasurePreserving.integral_comp`

English:
theorem MeasurePreserving.integral_comp
  statement: {β} {_ : MeasurableSpace β} {f : α -> β} {ν}
  proof: h₁.map_eq ▸ (h₂.integral_map g).symm

中文:
定理 保测.integral_comp
  结论: {β} {_ : 可测空间 β} {f : α -> β} {ν}
  证明: h₁.map_eq ▸ (h₂.integral_map g).symm

Depends on / 依赖: integral_map, map_eq
-/
theorem MeasurePreserving.integral_comp {β} {_ : MeasurableSpace β} {f : α -> β} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β -> G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν :=
  h₁.map_eq ▸ (h₂.integral_map g).symm

/--
theorem `MeasurePreserving.integral_comp'` / 定理 `MeasurePreserving.integral_comp'`

English:
theorem MeasurePreserving.integral_comp'
  statement: {β} [MeasurableSpace β] {ν} {f : α ≃ᵐ β}
  proof: MeasurePreserving.integral_comp h f.measurableEmbedding _

中文:
定理 保测.integral_comp'
  结论: {β} [可测空间 β] {ν} {f : α ≃ᵐ β}
  证明: MeasurePreserving.integral_comp h f.measurableEmbedding _

Depends on / 依赖: MeasurePreserving, MeasurePreserving.integral_comp, f.measurableEmbedding, integral_comp, measurableEmbedding
-/
theorem MeasurePreserving.integral_comp' {β} [MeasurableSpace β] {ν} {f : α ≃ᵐ β}
    (h : MeasurePreserving f μ ν) (g : β -> G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := MeasurePreserving.integral_comp h f.measurableEmbedding _

/--
theorem `integral_subtype_comap` / 定理 `integral_subtype_comap`

English:
theorem integral_subtype_comap
  statement: {α} [MeasurableSpace α] {μ : Measure α} {s : Set α}
  proof: by
  rw [← map_comap_subtype_coe hs]
  exact ((MeasurableEmbedding.subtype_coe hs).integral_map _).symm

中文:
定理 integral_subtype_comap
  结论: {α} [可测空间 α] {μ : 测度 α} {s : 集合 α}
  证明: by
  rw [← map_comap_subtype_coe hs]
  exact ((MeasurableEmbedding.subtype_coe hs).integral_map _).symm

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, integral_map, map_comap_subtype_coe, subtype_coe
-/
theorem integral_subtype_comap {α} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : α -> G) :
    ∫ x : s, f (x : α) ∂(Measure.comap Subtype.val μ) = ∫ x in s, f x ∂μ := by
  rw [← map_comap_subtype_coe hs]
  exact ((MeasurableEmbedding.subtype_coe hs).integral_map _).symm

attribute [local instance] Measure.Subtype.measureSpace in
/--
theorem `integral_subtype` / 定理 `integral_subtype`

English:
theorem integral_subtype
  given: {α} [MeasureSpace α] {s : Set α} (hs : MeasurableSet s) (f : α -> G)
  proof: integral_subtype_comap hs f

@[simp]

中文:
定理 integral_subtype
  条件: {α} [测度空间 α] {s : 集合 α} (hs : 可测集 s) (f : α -> G)
  证明: integral_subtype_comap hs f

@[simp]

Depends on / 依赖: integral_subtype_comap
-/
theorem integral_subtype {α} [MeasureSpace α] {s : Set α} (hs : MeasurableSet s) (f : α -> G) :
    ∫ x : s, f x = ∫ x in s, f x := integral_subtype_comap hs f

@[simp]
/--
theorem `integral_dirac'` / 定理 `integral_dirac'`

English:
theorem integral_dirac'
  given: [MeasurableSpace α] (f : α -> E) (a : α) (hfm : StronglyMeasurable f)
  proof: by
  borelize E
  calc
    ∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a :=
integral_congr_ae ae_eq_dirac' hfm.measurable
    _ = f a := by simp

@[simp]

中文:
定理 integral_dirac'
  条件: [可测空间 α] (f : α -> E) (a : α) (hfm : StronglyMeasurable f)
  证明: by
  borelize E
  calc
    ∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a :=
integral_congr_ae ae_eq_dirac' hfm.measurable
    _ = f a := by simp

@[simp]

Depends on / 依赖: Measure, Measure.dirac, ae_eq_dirac, borelize, hfm.measurable, integral_congr_ae, measurable
-/
theorem integral_dirac' [MeasurableSpace α] (f : α -> E) (a : α) (hfm : StronglyMeasurable f) :
    ∫ x, f x ∂Measure.dirac a = f a := by
  borelize E
  calc
    ∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a :=
integral_congr_ae ae_eq_dirac' hfm.measurable
    _ = f a := by simp

@[simp]
/--
theorem `integral_dirac` / 定理 `integral_dirac`

English:
theorem integral_dirac
  given: [MeasurableSpace α] [MeasurableSingletonClass α] (f : α -> E) (a : α)
  proof: calc
∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a := integral_congr_ae ae_eq_dirac f
    _ = f a := by simp

中文:
定理 integral_dirac
  条件: [可测空间 α] [MeasurableSingleton类 α] (f : α -> E) (a : α)
  证明: calc
∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a := integral_congr_ae ae_eq_dirac f
    _ = f a := by simp

Depends on / 依赖: Measure, Measure.dirac, ae_eq_dirac, integral_congr_ae
-/
theorem integral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α -> E) (a : α) :
    ∫ x, f x ∂Measure.dirac a = f a :=
  calc
∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a := integral_congr_ae ae_eq_dirac f
    _ = f a := by simp

/--
theorem `setIntegral_dirac'` / 定理 `setIntegral_dirac'`

English:
theorem setIntegral_dirac'
  statement: {mα : MeasurableSpace α} {f : α -> E} (hf : StronglyMeasurable f) (a : α)
  proof: by
  rw [restrict_dirac' hs]
  split_ifs
  · exact integral_dirac' _ _ hf
  · exact integral_zero_measure _

中文:
定理 set整数egral_dirac'
  结论: {mα : 可测空间 α} {f : α -> E} (hf : StronglyMeasurable f) (a : α)
  证明: by
  rw [restrict_dirac' hs]
  split_ifs
  · exact integral_dirac' _ _ hf
  · exact integral_zero_measure _

Depends on / 依赖: integral_dirac, integral_zero_measure, restrict_dirac, split_ifs
-/
theorem setIntegral_dirac' {mα : MeasurableSpace α} {f : α -> E} (hf : StronglyMeasurable f) (a : α)
    {s : Set α} (hs : MeasurableSet s) [Decidable (a in s)] :
    ∫ x in s, f x ∂Measure.dirac a = if a in s then f a else 0 := by
  rw [restrict_dirac' hs]
  split_ifs
  · exact integral_dirac' _ _ hf
  · exact integral_zero_measure _

/--
theorem `setIntegral_dirac` / 定理 `setIntegral_dirac`

English:
theorem setIntegral_dirac
  statement: [MeasurableSpace α] [MeasurableSingletonClass α] (f : α -> E) (a : α)
  proof: by
  rw [restrict_dirac]
  split_ifs
  · exact integral_dirac _ _
  · exact integral_zero_measure _

中文:
定理 set整数egral_dirac
  结论: [可测空间 α] [MeasurableSingleton类 α] (f : α -> E) (a : α)
  证明: by
  rw [restrict_dirac]
  split_ifs
  · exact integral_dirac _ _
  · exact integral_zero_measure _

Depends on / 依赖: integral_dirac, integral_zero_measure, restrict_dirac, split_ifs
-/
theorem setIntegral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α -> E) (a : α)
    (s : Set α) [Decidable (a in s)] :
    ∫ x in s, f x ∂Measure.dirac a = if a in s then f a else 0 := by
  rw [restrict_dirac]
  split_ifs
  · exact integral_dirac _ _
  · exact integral_zero_measure _

/--
theorem `mul_meas_ge_le_integral_of_nonneg` / 定理 `mul_meas_ge_le_integral_of_nonneg`

English:
theorem mul_meas_ge_le_integral_of_nonneg
  statement: {f : α -> Real} (hf_nonneg : 0 <=ᵐ[μ] f)
  proof: by
  rcases eq_top_or_lt_top (μ {x | ε <= f x}) with hμ | hμ
  · simpa [measureReal_def, hμ] using integral_nonneg_of_ae hf_nonneg
  · have := Fact.mk hμ
    calc
      ε * μ.real { x | ε <= f x } = ∫ _ in {x | ε <= f x}, ε ∂μ := by simp [mul_comm]
      _ <= ∫ x in {x | ε <= f x}, f x ∂μ :=
integra

中文:
定理 mul_meas_ge_le_integral_of_nonneg
  结论: {f : α -> 实数} (hf_nonneg : 0 <=ᵐ[μ] f)
  证明: by
  rcases eq_top_or_lt_top (μ {x | ε <= f x}) with hμ | hμ
  · simpa [measureReal_def, hμ] using integral_nonneg_of_ae hf_nonneg
  · have := Fact.mk hμ
    calc
      ε * μ.real { x | ε <= f x } = ∫ _ in {x | ε <= f x}, ε ∂μ := by simp [mul_comm]
      _ <= ∫ x in {x | ε <= f x}, f x ∂μ :=
integra

Depends on / 依赖: Fact.mk, aemeasurable, eq_top_or_lt_top, hf_int, hf_int.aemeasurable.nullMeasurable, hf_int.mono_measure, hf_nonneg, integrable_const, integral_mono_ae, integral_mono_measure, integral_nonneg_of_ae, measurableSet_Ici, measureReal_def, mono_measure, mul_comm, nullMeasurable, restrict_le_self
-/
theorem mul_meas_ge_le_integral_of_nonneg {f : α -> Real} (hf_nonneg : 0 <=ᵐ[μ] f)
    (hf_int : Integrable f μ) (ε : Real) : ε * μ.real { x | ε <= f x } <= ∫ x, f x ∂μ := by
  rcases eq_top_or_lt_top (μ {x | ε <= f x}) with hμ | hμ
  · simpa [measureReal_def, hμ] using integral_nonneg_of_ae hf_nonneg
  · have := Fact.mk hμ
    calc
      ε * μ.real { x | ε <= f x } = ∫ _ in {x | ε <= f x}, ε ∂μ := by simp [mul_comm]
      _ <= ∫ x in {x | ε <= f x}, f x ∂μ :=
integral_mono_ae (integrable_const _) (hf_int.mono_measure μ.restrict_le_self)
ae_restrict_mem₀ hf_int.aemeasurable.nullMeasurable measurableSet_Ici
      _ <= _ := integral_mono_measure μ.restrict_le_self hf_nonneg hf_int

/--
theorem `integral_mul_norm_le_Lp_mul_Lq` / 定理 `integral_mul_norm_le_Lp_mul_Lq`

English:
theorem integral_mul_norm_le_Lp_mul_Lq
  statement: {E} [NormedAddCommGroup E] {f g : α -> E} {p q : Real}
  proof: by
  -- translate the Bochner integrals into Lebesgue integrals.
  rw [integral_eq_lintegral_of_nonneg_ae]; rw [integral_eq_lintegral_of_nonneg_ae]; rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Eventually.of_forall fun x => by positivity
  · exact (hg.1.norm.aemeasurable.pow aemea

中文:
定理 integral_mul_norm_le_Lp_mul_Lq
  结论: {E} [赋范交换加群 E] {f g : α -> E} {p q : 实数}
  证明: by
  -- translate the Bochner integrals into Lebesgue integrals.
  rw [integral_eq_lintegral_of_nonneg_ae]; rw [integral_eq_lintegral_of_nonneg_ae]; rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Eventually.of_forall fun x => by positivity
  · exact (hg.1.norm.aemeasurable.pow aemea
-/
theorem integral_mul_norm_le_Lp_mul_Lq {E} [NormedAddCommGroup E] {f g : α -> E} {p q : Real}
    (hpq : p.HolderConjugate q) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ a, ‖f a‖ * ‖g a‖ ∂μ <= (∫ a, ‖f a‖ ^ p ∂μ) ^ (1 / p) * (∫ a, ‖g a‖ ^ q ∂μ) ^ (1 / q) := by
  -- translate the Bochner integrals into Lebesgue integrals.
  rw [integral_eq_lintegral_of_nonneg_ae]; rw [integral_eq_lintegral_of_nonneg_ae]; rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Eventually.of_forall fun x => by positivity
  · exact (hg.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by positivity
  · exact (hf.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by positivity
  · exact hf.1.norm.mul hg.1.norm
  rw [ENNReal.toReal_rpow]; rw [ENNReal.toReal_rpow]; rw [← ENNReal.toReal_mul]
  -- replace norms by nnnorm
  have h_left : ∫⁻ a, ENNReal.ofReal (‖f a‖ * ‖g a‖) ∂μ =
      ∫⁻ a, ((‖f ·‖ₑ) * (‖g ·‖ₑ)) a ∂μ := by
    simp_rw [Pi.mul_apply, ← ofReal_norm, ENNReal.ofReal_mul (norm_nonneg _)]
  have h_right_f : ∫⁻ a, .ofReal (‖f a‖ ^ p) ∂μ = ∫⁻ a, ‖f a‖ₑ ^ p ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm]; rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.nonneg]
  have h_right_g : ∫⁻ a, .ofReal (‖g a‖ ^ q) ∂μ = ∫⁻ a, ‖g a‖ₑ ^ q ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm]; rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.symm.nonneg]
  rw [h_left]; rw [h_right_f]; rw [h_right_g]
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

/--
theorem `integral_mul_le_Lp_mul_Lq_of_nonneg` / 定理 `integral_mul_le_Lp_mul_Lq_of_nonneg`

English:
theorem integral_mul_le_Lp_mul_Lq_of_nonneg
  statement: {p q : Real} (hpq : p.HolderConjugate q) {f g : α -> Real}
  proof: by
  have h_left : ∫ a, f a * g a ∂μ = ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg, hg_nonneg] with x hxf hxg
    rw [Real.norm_of_nonneg hxf]; rw [Real.norm_of_nonneg hxg]
  have h_right_f : ∫ a, f a ^ p ∂μ = ∫ a, ‖f a‖ ^ p ∂μ := by
    refine integral_

中文:
定理 integral_mul_le_Lp_mul_Lq_of_nonneg
  结论: {p q : 实数} (hpq : p.HolderConjugate q) {f g : α -> 实数}
  证明: by
  have h_left : ∫ a, f a * g a ∂μ = ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg, hg_nonneg] with x hxf hxg
    rw [Real.norm_of_nonneg hxf]; rw [Real.norm_of_nonneg hxg]
  have h_right_f : ∫ a, f a ^ p ∂μ = ∫ a, ‖f a‖ ^ p ∂μ := by
    refine integral_

Depends on / 依赖: Real.norm_of, Real.norm_of_nonneg, filter_upwards, h_left, h_right_f, h_right_g, hf_nonneg, hg_nonneg, integral_congr_ae, norm_of, norm_of_nonneg
-/
theorem integral_mul_le_Lp_mul_Lq_of_nonneg {p q : Real} (hpq : p.HolderConjugate q) {f g : α -> Real}
    (hf_nonneg : 0 <=ᵐ[μ] f) (hg_nonneg : 0 <=ᵐ[μ] g) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ a, f a * g a ∂μ <= (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q) := by
  have h_left : ∫ a, f a * g a ∂μ = ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg, hg_nonneg] with x hxf hxg
    rw [Real.norm_of_nonneg hxf]; rw [Real.norm_of_nonneg hxg]
  have h_right_f : ∫ a, f a ^ p ∂μ = ∫ a, ‖f a‖ ^ p ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg] with x hxf
    rw [Real.norm_of_nonneg hxf]
  have h_right_g : ∫ a, g a ^ q ∂μ = ∫ a, ‖g a‖ ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hg_nonneg] with x hxg
    rw [Real.norm_of_nonneg hxg]
  rw [h_left]; rw [h_right_f]; rw [h_right_g]
  exact integral_mul_norm_le_Lp_mul_Lq hpq hf hg

/--
theorem `integral_singleton'` / 定理 `integral_singleton'`

English:
theorem integral_singleton'
  given: {μ : Measure α} {f : α -> E} (hf : StronglyMeasurable f) (a : α)
  proof: by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac' f a hf,
    measureReal_def]

中文:
定理 integral_singleton'
  条件: {μ : 测度 α} {f : α -> E} (hf : StronglyMeasurable f) (a : α)
  证明: by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac' f a hf,
    measureReal_def]

Depends on / 依赖: Measure, Measure.restrict_singleton, integral_dirac, integral_smul_measure, measureReal_def, restrict_singleton
-/
theorem integral_singleton' {μ : Measure α} {f : α -> E} (hf : StronglyMeasurable f) (a : α) :
    ∫ a in {a}, f a ∂μ = μ.real {a} • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac' f a hf,
    measureReal_def]

/--
theorem `integral_singleton` / 定理 `integral_singleton`

English:
theorem integral_singleton
  given: [MeasurableSingletonClass α] {μ : Measure α} (f : α -> E) (a : α)
  proof: by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac, measureReal_def]

中文:
定理 integral_singleton
  条件: [MeasurableSingleton类 α] {μ : 测度 α} (f : α -> E) (a : α)
  证明: by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac, measureReal_def]

Depends on / 依赖: Measure, Measure.restrict_singleton, integral_dirac, integral_smul_measure, measureReal_def, restrict_singleton
-/
theorem integral_singleton [MeasurableSingletonClass α] {μ : Measure α} (f : α -> E) (a : α) :
    ∫ a in {a}, f a ∂μ = μ.real {a} • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac, measureReal_def]

/--
theorem `integral_unique` / 定理 `integral_unique`

English:
theorem integral_unique
  given: [Unique α] (f : α -> E)
  statement: ∫ x, f x ∂μ = μ.real univ • f default
  proof: calc
    ∫ x, f x ∂μ = ∫ _, f default ∂μ := by congr with x; congr; exact Unique.uniq _ x
    _ = μ.real univ • f default := by rw [integral_const]

中文:
定理 integral_unique
  条件: [唯一 α] (f : α -> E)
  结论: ∫ x, f x ∂μ = μ.real univ • f default
  证明: calc
    ∫ x, f x ∂μ = ∫ _, f default ∂μ := by congr with x; congr; exact Unique.uniq _ x
    _ = μ.real univ • f default := by rw [integral_const]

Depends on / 依赖: Unique, Unique.uniq, integral_const
-/
theorem integral_unique [Unique α] (f : α -> E) : ∫ x, f x ∂μ = μ.real univ • f default :=
  calc
    ∫ x, f x ∂μ = ∫ _, f default ∂μ := by congr with x; congr; exact Unique.uniq _ x
    _ = μ.real univ • f default := by rw [integral_const]

/--
theorem `integral_pos_of_integrable_nonneg_nonzero` / 定理 `integral_pos_of_integrable_nonneg_nonzero`

English:
theorem integral_pos_of_integrable_nonneg_nonzero
  statement: [TopologicalSpace α] [Measure.IsOpenPosMeasure μ]
  proof: (integral_pos_iff_support_of_nonneg f_nonneg f_int).2
    (IsOpen.measure_pos μ f_cont.isOpen_support ⟨x, f_x⟩)

中文:
定理 integral_pos_of_integrable_nonneg_nonzero
  结论: [拓扑空间 α] [测度.是OpenPosMeasure μ]
  证明: (integral_pos_iff_support_of_nonneg f_nonneg f_int).2
    (IsOpen.measure_pos μ f_cont.isOpen_support ⟨x, f_x⟩)

Depends on / 依赖: IsOpen, IsOpen.measure_pos, f_cont, f_cont.isOpen_support, f_int, f_nonneg, integral_pos_iff_support_of_nonneg, isOpen_support, measure_pos
-/
theorem integral_pos_of_integrable_nonneg_nonzero [TopologicalSpace α] [Measure.IsOpenPosMeasure μ]
    {f : α -> Real} {x : α} (f_cont : Continuous f) (f_int : Integrable f μ) (f_nonneg : 0 <= f)
    (f_x : f x != 0) : 0 < ∫ x, f x ∂μ :=
  (integral_pos_iff_support_of_nonneg f_nonneg f_int).2
    (IsOpen.measure_pos μ f_cont.isOpen_support ⟨x, f_x⟩)

end Properties

section IntegralTrim

variable {β γ : Type*} {m m0 : MeasurableSpace β} {μ : Measure β}

/--
Definition of `SimpleFunc.toLargerSpace` / `SimpleFunc.toLargerSpace` 的定义

English:
definition SimpleFunc.toLargerSpace
  signature: (hm : m <= m0) (f : @SimpleFunc β m γ)
  body: ⟨@SimpleFunc.toFun β m γ f, fun x => hm _ (@SimpleFunc.measurableSet_fiber β γ m f x),
    @SimpleFunc.finite_range β γ m f⟩

中文:
定义 SimpleFunc.toLargerSpace
  签名: (hm : m <= m0) (f : @SimpleFunc β m γ)
  定义体: ⟨@SimpleFunc.toFun β m γ f, fun x => hm _ (@SimpleFunc.measurableSet_fiber β γ m f x),
    @SimpleFunc.finite_range β γ m f⟩

Depends on / 依赖: SimpleFunc, SimpleFunc.finite_range, SimpleFunc.measurableSet_fiber, SimpleFunc.toFun, finite_range, measurableSet_fiber
-/
def SimpleFunc.toLargerSpace (hm : m <= m0) (f : @SimpleFunc β m γ) : SimpleFunc β γ :=
  ⟨@SimpleFunc.toFun β m γ f, fun x => hm _ (@SimpleFunc.measurableSet_fiber β γ m f x),
    @SimpleFunc.finite_range β γ m f⟩

/--
theorem `SimpleFunc.coe_toLargerSpace_eq` / 定理 `SimpleFunc.coe_toLargerSpace_eq`

English:
theorem SimpleFunc.coe_toLargerSpace_eq
  given: (hm : m <= m0) (f : @SimpleFunc β m γ)
  proof: rfl

中文:
定理 SimpleFunc.coe_toLargerSpace_eq
  条件: (hm : m <= m0) (f : @SimpleFunc β m γ)
  证明: rfl
-/
theorem SimpleFunc.coe_toLargerSpace_eq (hm : m <= m0) (f : @SimpleFunc β m γ) :
    ⇑(f.toLargerSpace hm) = f := rfl

/--
theorem `integral_simpleFunc_larger_space` / 定理 `integral_simpleFunc_larger_space`

English:
theorem integral_simpleFunc_larger_space
  statement: (hm : m <= m0) (f : @SimpleFunc β m F)
  proof: by
  simp_rw [← f.coe_toLargerSpace_eq hm]
  rw [SimpleFunc.integral_eq_sum _ hf_int]
  congr 1

中文:
定理 integral_simpleFunc_larger_space
  结论: (hm : m <= m0) (f : @SimpleFunc β m F)
  证明: by
  simp_rw [← f.coe_toLargerSpace_eq hm]
  rw [SimpleFunc.integral_eq_sum _ hf_int]
  congr 1

Depends on / 依赖: SimpleFunc, SimpleFunc.integral_eq_sum, coe_toLargerSpace_eq, f.coe_toLargerSpace_eq, hf_int, integral_eq_sum, simp_rw
-/
theorem integral_simpleFunc_larger_space (hm : m <= m0) (f : @SimpleFunc β m F)
    (hf_int : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x in @SimpleFunc.range β F m f, μ.real (f ⁻¹' {x}) • x := by
  simp_rw [← f.coe_toLargerSpace_eq hm]
  rw [SimpleFunc.integral_eq_sum _ hf_int]
  congr 1

/--
theorem `integral_trim_simpleFunc` / 定理 `integral_trim_simpleFunc`

English:
theorem integral_trim_simpleFunc
  given: (hm : m <= m0) (f : @SimpleFunc β m F) (hf_int : Integrable f μ)
  proof: by
  have hf : StronglyMeasurable[m] f := @SimpleFunc.stronglyMeasurable β F m _ f
  have hf_int_m := hf_int.trim hm hf
  rw [integral_simpleFunc_larger_space (le_refl m) f hf_int_m]; rw [integral_simpleFunc_larger_space hm f hf_int]
  congr with x
  simp only [measureReal_def]
  congr 2
  exact (tr

中文:
定理 integral_trim_simpleFunc
  条件: (hm : m <= m0) (f : @SimpleFunc β m F) (hf_int : 可积 f μ)
  证明: by
  have hf : StronglyMeasurable[m] f := @SimpleFunc.stronglyMeasurable β F m _ f
  have hf_int_m := hf_int.trim hm hf
  rw [integral_simpleFunc_larger_space (le_refl m) f hf_int_m]; rw [integral_simpleFunc_larger_space hm f hf_int]
  congr with x
  simp only [measureReal_def]
  congr 2
  exact (tr

Depends on / 依赖: SimpleFunc, SimpleFunc.measurableSet_fiber, SimpleFunc.stronglyMeasurable, StronglyMeasurable, hf_int, hf_int.trim, hf_int_m, integral_simpleFunc_larger_space, le_refl, measurableSet_fiber, measureReal_def, stronglyMeasurable, trim_measurableSet_eq
-/
theorem integral_trim_simpleFunc (hm : m <= m0) (f : @SimpleFunc β m F) (hf_int : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  have hf : StronglyMeasurable[m] f := @SimpleFunc.stronglyMeasurable β F m _ f
  have hf_int_m := hf_int.trim hm hf
  rw [integral_simpleFunc_larger_space (le_refl m) f hf_int_m]; rw [integral_simpleFunc_larger_space hm f hf_int]
  congr with x
  simp only [measureReal_def]
  congr 2
  exact (trim_measurableSet_eq hm (@SimpleFunc.measurableSet_fiber β F m f x)).symm

/--
theorem `integral_trim` / 定理 `integral_trim`

English:
theorem integral_trim
  given: (hm : m <= m0) {f : β -> G} (hf : StronglyMeasurable[m] f)
  proof: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  borelize G
  by_cases hf_int : Integrable f μ
  swap
  · have hf_int_m : ¬Integrable f (μ.trim hm) := fun hf_int_m =>
      hf_int (integrable_of_integrable_trim hm hf_int_m)
    rw [integral_undef hf_int]; rw [integral_undef hf_int_

中文:
定理 integral_trim
  条件: (hm : m <= m0) {f : β -> G} (hf : StronglyMeasurable[m] f)
  证明: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  borelize G
  by_cases hf_int : Integrable f μ
  swap
  · have hf_int_m : ¬Integrable f (μ.trim hm) := fun hf_int_m =>
      hf_int (integrable_of_integrable_trim hm hf_int_m)
    rw [integral_undef hf_int]; rw [integral_undef hf_int_

Depends on / 依赖: CompleteSpace, Integrable, SeparableSpace, SimpleFunc, SimpleFunc.approxOn, approxOn, borelize, f_seq, hf.measurable, hf.separableSpace_range_union_singleton, hf_int, hf_int_m, hf_seq_meas, integrable_of_integrable_trim, integral, integral_undef, measurable, separableSpace_range_union_singleton
-/
theorem integral_trim (hm : m <= m0) {f : β -> G} (hf : StronglyMeasurable[m] f) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  borelize G
  by_cases hf_int : Integrable f μ
  swap
  · have hf_int_m : ¬Integrable f (μ.trim hm) := fun hf_int_m =>
      hf_int (integrable_of_integrable_trim hm hf_int_m)
    rw [integral_undef hf_int]; rw [integral_undef hf_int_m]
  have : SeparableSpace (range f union {0} : Set G) := hf.separableSpace_range_union_singleton
  let f_seq := @SimpleFunc.approxOn G β _ _ _ m _ hf.measurable (range f union {0}) 0 (by simp) _
  have hf_seq_meas : forall n, StronglyMeasurable[m] (f_seq n) := fun n =>
    @SimpleFunc.stronglyMeasurable β G m _ (f_seq n)
  have hf_seq_int : forall n, Integrable (f_seq n) μ :=
    SimpleFunc.integrable_approxOn_range (hf.mono hm).measurable hf_int
  have hf_seq_int_m : forall n, Integrable (f_seq n) (μ.trim hm) := fun n =>
    (hf_seq_int n).trim hm (hf_seq_meas n)
  have hf_seq_eq : forall n, ∫ x, f_seq n x ∂μ = ∫ x, f_seq n x ∂μ.trim hm := fun n =>
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

/--
theorem `integral_trim_ae` / 定理 `integral_trim_ae`

English:
theorem integral_trim_ae
  given: (hm : m <= m0) {f : β -> G} (hf : AEStronglyMeasurable[m] f (μ.trim hm))
  proof: by
  rw [integral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]; rw [integral_congr_ae hf.ae_eq_mk]
  exact integral_trim hm hf.stronglyMeasurable_mk

中文:
定理 integral_trim_ae
  条件: (hm : m <= m0) {f : β -> G} (hf : AEStronglyMeasurable[m] f (μ.trim hm))
  证明: by
  rw [integral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]; rw [integral_congr_ae hf.ae_eq_mk]
  exact integral_trim hm hf.stronglyMeasurable_mk

Depends on / 依赖: ae_eq_mk, ae_eq_of_ae_eq_trim, hf.ae_eq_mk, hf.stronglyMeasurable_mk, integral_congr_ae, integral_trim, stronglyMeasurable_mk
-/
theorem integral_trim_ae (hm : m <= m0) {f : β -> G} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  rw [integral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]; rw [integral_congr_ae hf.ae_eq_mk]
  exact integral_trim hm hf.stronglyMeasurable_mk

end IntegralTrim

section SnormBound

variable {m0 : MeasurableSpace α} {μ : Measure α} {f : α -> Real}

/--
theorem `eLpNorm_one_le_of_le` / 定理 `eLpNorm_one_le_of_le`

English:
theorem eLpNorm_one_le_of_le
  statement: {r : Real>=0} (hfint : Integrable f μ) (hfint' : 0 <= ∫ x, f x ∂μ)
  proof: by
  by_cases hr : r = 0
  · suffices f =ᵐ[μ] 0 by
      rw [eLpNorm_congr_ae this]; rw [eLpNorm_zero]; rw [hr]; rw [ENNReal.coe_zero]; rw [mul_zero]
    rw [hr] at hf
    norm_cast at hf
    have hnegf : ∫ x, -f x ∂μ = 0 := by
      rw [integral_neg]; rw [neg_eq_zero]
      exact le_antisymm (integ

中文:
定理 eLpNorm_one_le_of_le
  结论: {r : 实数>=0} (hfint : 可积 f μ) (hfint' : 0 <= ∫ x, f x ∂μ)
  证明: by
  by_cases hr : r = 0
  · suffices f =ᵐ[μ] 0 by
      rw [eLpNorm_congr_ae this]; rw [eLpNorm_zero]; rw [hr]; rw [ENNReal.coe_zero]; rw [mul_zero]
    rw [hr] at hf
    norm_cast at hf
    have hnegf : ∫ x, -f x ∂μ = 0 := by
      rw [integral_neg]; rw [neg_eq_zero]
      exact le_antisymm (integ

Depends on / 依赖: ENNReal, ENNReal.coe_zero, Pi.neg_apply, Pi.zero_apply, coe_zero, eLpNorm_congr_ae, eLpNorm_zero, filter_upwards, hfint.neg, integral_eq_zero_iff_of_nonneg_ae, integral_neg, integral_nonpos_of_ae, le_antisymm, mul_zero, neg_apply, neg_eq_zero, zero_apply
-/
theorem eLpNorm_one_le_of_le {r : Real>=0} (hfint : Integrable f μ) (hfint' : 0 <= ∫ x, f x ∂μ)
    (hf : forallᵐ ω ∂μ, f ω <= r) : eLpNorm f 1 μ <= 2 * μ Set.univ * r := by
  by_cases hr : r = 0
  · suffices f =ᵐ[μ] 0 by
      rw [eLpNorm_congr_ae this]; rw [eLpNorm_zero]; rw [hr]; rw [ENNReal.coe_zero]; rw [mul_zero]
    rw [hr] at hf
    norm_cast at hf
    have hnegf : ∫ x, -f x ∂μ = 0 := by
      rw [integral_neg]; rw [neg_eq_zero]
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
    rw [this]; rw [ENNReal.mul_top']; rw [if_neg]; rw [ENNReal.top_mul']; rw [if_neg]
    · exact le_top
    · simp [hr]
    · simp
  have := hμ
  rw [integral_eq_integral_pos_part_sub_integral_neg_part hfint]; rw [sub_nonneg] at hfint'
  have hposbdd : ∫ ω, max (f ω) 0 ∂μ <= μ.real Set.univ • (r : Real) := by
    rw [← integral_const]
    refine integral_mono_ae hfint.real_toNNReal (integrable_const (r : Real)) ?_
    filter_upwards [hf] with ω hω using Real.toNNReal_le_iff_le_coe.2 hω
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
      (memLp_one_iff_integrable.2 hfint)]; rw [ENNReal.ofReal_le_iff_le_toReal (by finiteness)]
  simp_rw [ENNReal.toReal_one, _root_.inv_one, Real.rpow_one, Real.norm_eq_abs, ←
    max_zero_add_max_neg_zero_eq_abs_self, ← Real.coe_toNNReal']
  rw [integral_add hfint.real_toNNReal]
  · simp only [Real.coe_toNNReal', ENNReal.toReal_mul, ENNReal.coe_toReal,
      toReal_ofNat] at hfint' ⊢
    grw [hfint']
    rwa [← two_mul, mul_assoc, mul_le_mul_iff_right₀ (two_pos : (0 : Real) < 2)]
  · exact hfint.neg.sup (integrable_zero _ _ μ)

/--
theorem `eLpNorm_one_le_of_le'` / 定理 `eLpNorm_one_le_of_le'`

English:
theorem eLpNorm_one_le_of_le'
  statement: {r : Real} (hfint : Integrable f μ) (hfint' : 0 <= ∫ x, f x ∂μ)
  proof: by
  refine eLpNorm_one_le_of_le hfint hfint' ?_
  simp only [Real.coe_toNNReal', le_max_iff]
  filter_upwards [hf] with ω hω using Or.inl hω

中文:
定理 eLpNorm_one_le_of_le'
  结论: {r : 实数} (hfint : 可积 f μ) (hfint' : 0 <= ∫ x, f x ∂μ)
  证明: by
  refine eLpNorm_one_le_of_le hfint hfint' ?_
  simp only [Real.coe_toNNReal', le_max_iff]
  filter_upwards [hf] with ω hω using Or.inl hω

Depends on / 依赖: Or.inl, Real.coe_toNNReal, coe_toNNReal, eLpNorm_one_le_of_le, filter_upwards, le_max_iff
-/
theorem eLpNorm_one_le_of_le' {r : Real} (hfint : Integrable f μ) (hfint' : 0 <= ∫ x, f x ∂μ)
    (hf : forallᵐ ω ∂μ, f ω <= r) : eLpNorm f 1 μ <= 2 * μ Set.univ * ENNReal.ofReal r := by
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
  | 0, ~q(Real), ~q(@MeasureTheory.integral $i Real _ $inst2 _ _ $f) =>
    let i : Q($i) ← mkFreshExprMVarQ q($i) .syntheticOpaque
    have body : Q(Real) := .betaRev f #[i]
    let rbody ← core zα pα body
    let pbody ← rbody.toNonneg
    let pr : Q(forall x, 0 <= $f x) ← mkLambdaFVars #[i] pbody
    assertInstancesCommute
    return .nonnegative q(integral_nonneg $pr)
  | _ => throwError "not MeasureTheory.integral"

end Mathlib.Meta.Positivity
