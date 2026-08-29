/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # Conditional expectation in L1

This file contains two more steps of the construction of the conditional expectation, which is
completed in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`. See that file for a
description of the full process.

The conditional expectation of an `L²` function is defined in
`MeasureTheory.Function.ConditionalExpectation.CondexpL2`. In this file, we perform two steps.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).

## Main definitions

* `condExpL1`: Conditional expectation of a function as a linear map from `L1` to itself.

-/

@[expose] public section


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α F F' G G' 𝕜 : Type*} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace Real F']
  -- G for a Lp add_subgroup
  [NormedAddCommGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedAddCommGroup G']
  [NormedSpace Real G'] [CompleteSpace G']

section CondexpInd

/-! ## Conditional expectation of an indicator as a continuous linear map.

The goal of this section is to build
`condExpInd (hm : m ≤ m0) (μ : Measure α) (s : Set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/


variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedSpace Real G]

section CondexpIndL1Fin


/--
Definition of `condExpIndL1Fin` / `condExpIndL1Fin` 的定义

English:
definition condExpIndL1Fin
  signature: (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s != ∞)
  body: (integrable_condExpIndSMul hm hs hμs x).toL1 _

中文:
定义 condExpIndL1Fin
  签名: (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s != ∞)
  定义体: (integrable_condExpIndSMul hm hs hμs x).toL1 _

Depends on / 依赖: integrable_condExpIndSMul
-/
def condExpIndL1Fin (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s != ∞)
    (x : G) : α ->₁[μ] G :=
  (integrable_condExpIndSMul hm hs hμs x).toL1 _

/--
theorem `condExpIndL1Fin_ae_eq_condExpIndSMul` / 定理 `condExpIndL1Fin_ae_eq_condExpIndSMul`

English:
theorem condExpIndL1Fin_ae_eq_condExpIndSMul
  statement: (hm : m <= m0) [SigmaFinite (μ.trim hm)]
  proof: (integrable_condExpIndSMul hm hs hμs x).coeFn_toL1

中文:
定理 condExpIndL1Fin_ae_eq_condExpIndSMul
  结论: (hm : m <= m0) [SigmaFinite (μ.trim hm)]
  证明: (integrable_condExpIndSMul hm hs hμs x).coeFn_toL1

Depends on / 依赖: coeFn_toL1, integrable_condExpIndSMul
-/
theorem condExpIndL1Fin_ae_eq_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) :
    condExpIndL1Fin hm hs hμs x =ᵐ[μ] condExpIndSMul hm hs hμs x :=
  (integrable_condExpIndSMul hm hs hμs x).coeFn_toL1

variable {hm : m <= m0} [SigmaFinite (μ.trim hm)]

-- Porting note: this lemma fills the hole in `refine' (MemLp.coeFn_toLp _) ...`
-- which is not automatically filled in Lean 4
/--
theorem `q` / 定理 `q`

English:
theorem q
  given: {hs : MeasurableSet s} {hμs : μ s != ∞} {x : G}
  proof: by
  rw [memLp_one_iff_integrable]; apply integrable_condExpIndSMul

中文:
定理 q
  条件: {hs : MeasurableSet s} {hμs : μ s != ∞} {x : G}
  证明: by
  rw [memLp_one_iff_integrable]; apply integrable_condExpIndSMul
-/
private theorem q {hs : MeasurableSet s} {hμs : μ s != ∞} {x : G} :
    MemLp (condExpIndSMul hm hs hμs x) 1 μ := by
  rw [memLp_one_iff_integrable]; apply integrable_condExpIndSMul

/--
theorem `condExpIndL1Fin_add` / 定理 `condExpIndL1Fin_add`

English:
theorem condExpIndL1Fin_add
  given: (hs : MeasurableSet s) (hμs : μ s != ∞) (x y : G)
  proof: by
  ext1
  unfold condExpIndL1Fin Integrable.toL1
  grw [Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp, MemLp.coeFn_toLp, condExpIndSMul_add,
    Lp.coeFn_add]

中文:
定理 condExpIndL1Fin_add
  条件: (hs : MeasurableSet s) (hμs : μ s != ∞) (x y : G)
  证明: by
  ext1
  unfold condExpIndL1Fin Integrable.toL1
  grw [Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp, MemLp.coeFn_toLp, condExpIndSMul_add,
    Lp.coeFn_add]

Depends on / 依赖: Integrable, Integrable.toL1, Lp.coeFn_add, MemLp.coeFn_toLp, coeFn_add, coeFn_toLp, condExpIndL1Fin, condExpIndSMul_add
-/
theorem condExpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s != ∞) (x y : G) :
    condExpIndL1Fin hm hs hμs (x + y) =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm hs hμs y := by
  ext1
  unfold condExpIndL1Fin Integrable.toL1
  grw [Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp, MemLp.coeFn_toLp, condExpIndSMul_add,
    Lp.coeFn_add]

/--
theorem `condExpIndL1Fin_smul` / 定理 `condExpIndL1Fin_smul`

English:
theorem condExpIndL1Fin_smul
  given: (hs : MeasurableSet s) (hμs : μ s != ∞) (c : Real) (x : G)
  proof: by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

中文:
定理 condExpIndL1Fin_smul
  条件: (hs : MeasurableSet s) (hμs : μ s != ∞) (c : 实数) (x : G)
  证明: by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

Depends on / 依赖: Lp.coeFn_smul, coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndSMul_smul
-/
theorem condExpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s != ∞) (c : Real) (x : G) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

/--
theorem `condExpIndL1Fin_smul'` / 定理 `condExpIndL1Fin_smul'`

English:
theorem condExpIndL1Fin_smul'
  statement: [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (hs : MeasurableSet s)
  proof: by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

中文:
定理 condExpIndL1Fin_smul'
  结论: [NormedSpace 实数 F] [SMulCommClass 实数 𝕜 F] (hs : MeasurableSet s)
  证明: by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

Depends on / 依赖: Lp.coeFn_smul, coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndSMul_smul
-/
theorem condExpIndL1Fin_smul' [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s != ∞) (c : 𝕜) (x : F) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

/--
theorem `norm_condExpIndL1Fin_le` / 定理 `norm_condExpIndL1Fin_le`

English:
theorem norm_condExpIndL1Fin_le
  given: (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G)
  proof: by
  rw [L1.norm_eq_integral_norm]; rw [← ENNReal.toReal_ofReal (norm_nonneg x)]; rw [measureReal_def]; rw [← ENNReal.toReal_mul]; rw [← ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top)]; rw [ofReal_integral_norm_eq_lintegral_enorm]
  swap; · rw [← memLp_one_iff_integra

中文:
定理 norm_condExpIndL1Fin_le
  条件: (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G)
  证明: by
  rw [L1.norm_eq_integral_norm]; rw [← ENNReal.toReal_ofReal (norm_nonneg x)]; rw [measureReal_def]; rw [← ENNReal.toReal_mul]; rw [← ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top)]; rw [ofReal_integral_norm_eq_lintegral_enorm]
  swap; · rw [← memLp_one_iff_integra

Depends on / 依赖: ENNReal, ENNReal.mul_ne_top, ENNReal.ofReal_le_iff_le_toReal, ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_ofReal, L1.norm_eq_integral_norm, Lp.memLp, condExpIndL1Fin, condExpIndL1Fin_ae_eq_condExpIndS, condExpIndSMul, filter_upwards, h_eq, lintegral_congr_ae, measureReal_def, memLp_one_iff_integrable, mul_ne_top, norm_eq_integral_norm, norm_nonneg, ofReal_integral_norm_eq_lintegral_enorm
-/
theorem norm_condExpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) :
    ‖condExpIndL1Fin hm hs hμs x‖ <= μ.real s * ‖x‖ := by
  rw [L1.norm_eq_integral_norm]; rw [← ENNReal.toReal_ofReal (norm_nonneg x)]; rw [measureReal_def]; rw [← ENNReal.toReal_mul]; rw [← ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top)]; rw [ofReal_integral_norm_eq_lintegral_enorm]
  swap; · rw [← memLp_one_iff_integrable]; exact Lp.memLp _
  have h_eq :
    ∫⁻ a, ‖condExpIndL1Fin hm hs hμs x a‖ₑ ∂μ = ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖ₑ ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x] with z hz
    rw [hz]
  rw [h_eq]; rw [ofReal_norm]
  exact lintegral_nnnorm_condExpIndSMul_le hm hs hμs x

/--
theorem `condExpIndL1Fin_disjoint_union` / 定理 `condExpIndL1Fin_disjoint_union`

English:
theorem condExpIndL1Fin_disjoint_union
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞)
  proof: by
  ext1
  grw [Lp.coeFn_add, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndL1Fin_ae_eq_condExpIndSMul]
  rw [condExpIndSMul]
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : Real)]
  rw [map_add]
  push_cast
  rw [map_add]
  grw [Lp.coeFn_add

中文:
定理 condExpIndL1Fin_disjoint_union
  结论: (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞)
  证明: by
  ext1
  grw [Lp.coeFn_add, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndL1Fin_ae_eq_condExpIndSMul]
  rw [condExpIndSMul]
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : Real)]
  rw [map_add]
  push_cast
  rw [map_add]
  grw [Lp.coeFn_add

Depends on / 依赖: Lp.coeFn_add, coeFn_add, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndSMul, indicatorConstLp_disjoint_union, map_add
-/
theorem condExpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞)
    (hμt : μ t != ∞) (hst : Disjoint s t) (x : G) :
    condExpIndL1Fin hm (hs.union ht) ((measure_union_le s t).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm ht hμt x := by
  ext1
  grw [Lp.coeFn_add, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndL1Fin_ae_eq_condExpIndSMul]
  rw [condExpIndSMul]
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : Real)]
  rw [map_add]
  push_cast
  rw [map_add]
  grw [Lp.coeFn_add]
  rfl

end CondexpIndL1Fin

section CondexpIndL1


open scoped Classical in
/--
Definition of `condExpIndL1` / `condExpIndL1` 的定义

English:
definition condExpIndL1
  signature: {m m0 : MeasurableSpace α} (hm : m <= m0) (μ : Measure α) (s : Set α)
  body: if hs : MeasurableSet s ∧ μ s != ∞ then condExpIndL1Fin hm hs.1 hs.2 x else 0

中文:
定义 condExpIndL1
  签名: {m m0 : MeasurableSpace α} (hm : m <= m0) (μ : Measure α) (s : Set α)
  定义体: if hs : MeasurableSet s ∧ μ s != ∞ then condExpIndL1Fin hm hs.1 hs.2 x else 0

Depends on / 依赖: MeasurableSet, condExpIndL1Fin
-/
def condExpIndL1 {m m0 : MeasurableSpace α} (hm : m <= m0) (μ : Measure α) (s : Set α)
    [SigmaFinite (μ.trim hm)] (x : G) : α ->₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s != ∞ then condExpIndL1Fin hm hs.1 hs.2 x else 0

variable {hm : m <= m0} [SigmaFinite (μ.trim hm)]

/--
theorem `condExpIndL1_of_measurableSet_of_measure_ne_top` / 定理 `condExpIndL1_of_measurableSet_of_measure_ne_top`

English:
theorem condExpIndL1_of_measurableSet_of_measure_ne_top
  statement: (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: by
  simp only [condExpIndL1, And.intro hs hμs, dif_pos, Ne, not_false_iff, and_self_iff]

中文:
定理 condExpIndL1_of_measurableSet_of_measure_ne_top
  结论: (hs : MeasurableSet s) (hμs : μ s != ∞)
  证明: by
  simp only [condExpIndL1, And.intro hs hμs, dif_pos, Ne, not_false_iff, and_self_iff]

Depends on / 依赖: And.intro, and_self_iff, condExpIndL1, dif_pos, not_false_iff
-/
theorem condExpIndL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s != ∞)
    (x : G) : condExpIndL1 hm μ s x = condExpIndL1Fin hm hs hμs x := by
  simp only [condExpIndL1, And.intro hs hμs, dif_pos, Ne, not_false_iff, and_self_iff]

/--
theorem `condExpIndL1_of_measure_eq_top` / 定理 `condExpIndL1_of_measure_eq_top`

English:
theorem condExpIndL1_of_measure_eq_top
  given: (hμs : μ s = ∞) (x : G)
  statement: condExpIndL1 hm μ s x = 0
  proof: by
  simp only [condExpIndL1, hμs, not_true, Ne, dif_neg, not_false_iff,
    and_false]

中文:
定理 condExpIndL1_of_measure_eq_top
  条件: (hμs : μ s = ∞) (x : G)
  结论: condExpIndL1 hm μ s x = 0
  证明: by
  simp only [condExpIndL1, hμs, not_true, Ne, dif_neg, not_false_iff,
    and_false]

Depends on / 依赖: and_false, condExpIndL1, dif_neg, not_false_iff, not_true
-/
theorem condExpIndL1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condExpIndL1 hm μ s x = 0 := by
  simp only [condExpIndL1, hμs, not_true, Ne, dif_neg, not_false_iff,
    and_false]

/--
theorem `condExpIndL1_of_not_measurableSet` / 定理 `condExpIndL1_of_not_measurableSet`

English:
theorem condExpIndL1_of_not_measurableSet
  given: (hs : ¬MeasurableSet s) (x : G)
  proof: by
  simp only [condExpIndL1, hs, dif_neg, not_false_iff, false_and]

中文:
定理 condExpIndL1_of_not_measurableSet
  条件: (hs : ¬MeasurableSet s) (x : G)
  证明: by
  simp only [condExpIndL1, hs, dif_neg, not_false_iff, false_and]

Depends on / 依赖: condExpIndL1, dif_neg, false_and, not_false_iff
-/
theorem condExpIndL1_of_not_measurableSet (hs : ¬MeasurableSet s) (x : G) :
    condExpIndL1 hm μ s x = 0 := by
  simp only [condExpIndL1, hs, dif_neg, not_false_iff, false_and]

/--
theorem `condExpIndL1_add` / 定理 `condExpIndL1_add`

English:
theorem condExpIndL1_add
  given: (x y : G)
  proof: by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [zero_add]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [zero_add]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_add hs hμ

中文:
定理 condExpIndL1_add
  条件: (x y : G)
  证明: by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [zero_add]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [zero_add]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_add hs hμ

Depends on / 依赖: MeasurableSet, condExpIndL1Fin_add, condExpIndL1_of_measurableSet_of_measure_ne_top, condExpIndL1_of_measure_eq_top, condExpIndL1_of_not_measurableSet, simp_rw, zero_add
-/
theorem condExpIndL1_add (x y : G) :
    condExpIndL1 hm μ s (x + y) = condExpIndL1 hm μ s x + condExpIndL1 hm μ s y := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [zero_add]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [zero_add]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_add hs hμs x y

/--
theorem `condExpIndL1_smul` / 定理 `condExpIndL1_smul`

English:
theorem condExpIndL1_smul
  given: (c : Real) (x : G)
  proof: by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul hs

中文:
定理 condExpIndL1_smul
  条件: (c : 实数) (x : G)
  证明: by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul hs

Depends on / 依赖: MeasurableSet, condExpIndL1Fin_smul, condExpIndL1_of_measurableSet_of_measure_ne_top, condExpIndL1_of_measure_eq_top, condExpIndL1_of_not_measurableSet, simp_rw, smul_zero
-/
theorem condExpIndL1_smul (c : Real) (x : G) :
    condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul hs hμs c x

/--
theorem `condExpIndL1_smul'` / 定理 `condExpIndL1_smul'`

English:
theorem condExpIndL1_smul'
  given: [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (c : 𝕜) (x : F)
  proof: by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul' h

中文:
定理 condExpIndL1_smul'
  条件: [NormedSpace 实数 F] [SMulCommClass 实数 𝕜 F] (c : 𝕜) (x : F)
  证明: by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul' h

Depends on / 依赖: MeasurableSet, condExpIndL1Fin_smul, condExpIndL1_of_measurableSet_of_measure_ne_top, condExpIndL1_of_measure_eq_top, condExpIndL1_of_not_measurableSet, simp_rw, smul_zero
-/
theorem condExpIndL1_smul' [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (c : 𝕜) (x : F) :
    condExpIndL1 hm μ s (c • x) = c • condExpIndL1 hm μ s x := by
  by_cases hs : MeasurableSet s
  swap; · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condExpIndL1_of_measure_eq_top hμs]; rw [smul_zero]
  · simp_rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condExpIndL1Fin_smul' hs hμs c x

/--
theorem `norm_condExpIndL1_le` / 定理 `norm_condExpIndL1_le`

English:
theorem norm_condExpIndL1_le
  given: (x : G)
  statement: ‖condExpIndL1 hm μ s x‖ <= μ.real s * ‖x‖
  proof: by
  by_cases hs : MeasurableSet s
  swap
  · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  by_cases hμs : μ s = ∞
  · rw [condExpIndL1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (

中文:
定理 norm_condExpIndL1_le
  条件: (x : G)
  结论: ‖condExpIndL1 hm μ s x‖ <= μ.real s * ‖x‖
  证明: by
  by_cases hs : MeasurableSet s
  swap
  · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  by_cases hμs : μ s = ∞
  · rw [condExpIndL1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Lp.norm_zero, MeasurableSet, condExpIndL1_of_measurableSet_of_measure_ne_top, condExpIndL1_of_measure_eq_top, condExpIndL1_of_not_measurableSet, mul_nonneg, norm_condExpIndL1Fin_le, norm_nonneg, norm_zero, simp_rw, toReal_nonneg
-/
theorem norm_condExpIndL1_le (x : G) : ‖condExpIndL1 hm μ s x‖ <= μ.real s * ‖x‖ := by
  by_cases hs : MeasurableSet s
  swap
  · simp_rw [condExpIndL1_of_not_measurableSet hs]; rw [Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  by_cases hμs : μ s = ∞
  · rw [condExpIndL1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  · rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]
    exact norm_condExpIndL1Fin_le hs hμs x

/--
theorem `continuous_condExpIndL1` / 定理 `continuous_condExpIndL1`

English:
theorem continuous_condExpIndL1
  statement: Continuous fun x : G => condExpIndL1 hm μ s x
  proof: continuous_of_linear_of_bound condExpIndL1_add condExpIndL1_smul norm_condExpIndL1_le

中文:
定理 continuous_condExpIndL1
  结论: Continuous fun x : G => condExpIndL1 hm μ s x
  证明: continuous_of_linear_of_bound condExpIndL1_add condExpIndL1_smul norm_condExpIndL1_le

Depends on / 依赖: condExpIndL1_add, condExpIndL1_smul, continuous_of_linear_of_bound, norm_condExpIndL1_le
-/
theorem continuous_condExpIndL1 : Continuous fun x : G => condExpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condExpIndL1_add condExpIndL1_smul norm_condExpIndL1_le

/--
theorem `condExpIndL1_disjoint_union` / 定理 `condExpIndL1_disjoint_union`

English:
theorem condExpIndL1_disjoint_union
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞)
  proof: by
  have hμst : μ (s union t) != ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]; rw [condExpIndL1_of_measurableSet_of_measure_ne_top ht hμt x]; rw [condExpIndL1_of_measurableSe

中文:
定理 condExpIndL1_disjoint_union
  结论: (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞)
  证明: by
  have hμst : μ (s union t) != ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]; rw [condExpIndL1_of_measurableSet_of_measure_ne_top ht hμt x]; rw [condExpIndL1_of_measurableSe

Depends on / 依赖: ENNReal, ENNReal.add_ne_top.mpr, add_ne_top, condExpIndL1Fin_disjoint_union, condExpIndL1_of_measurableSet_of_measure_ne_top, hs.union, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, measure_union_le, trans_lt
-/
theorem condExpIndL1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞)
    (hμt : μ t != ∞) (hst : Disjoint s t) (x : G) :
    condExpIndL1 hm μ (s union t) x = condExpIndL1 hm μ s x + condExpIndL1 hm μ t x := by
  have hμst : μ (s union t) != ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  rw [condExpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]; rw [condExpIndL1_of_measurableSet_of_measure_ne_top ht hμt x]; rw [condExpIndL1_of_measurableSet_of_measure_ne_top (hs.union ht) hμst x]
  exact condExpIndL1Fin_disjoint_union hs ht hμs hμt hst x

end CondexpIndL1

variable (G)

/--
Definition of `condExpInd` / `condExpInd` 的定义

English:
definition condExpInd
  signature: {m m0 : MeasurableSpace α} (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
  body: condExpIndL1 hm μ s
  map_add' := condExpIndL1_add
  map_smul' := condExpIndL1_smul
  cont := continuous_condExpIndL1

中文:
定义 condExpInd
  签名: {m m0 : MeasurableSpace α} (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
  定义体: condExpIndL1 hm μ s
  map_add' := condExpIndL1_add
  map_smul' := condExpIndL1_smul
  cont := continuous_condExpIndL1

Depends on / 依赖: condExpIndL1
-/
def condExpInd {m m0 : MeasurableSpace α} (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (s : Set α) : G ->L[Real] α ->₁[μ] G where
  toFun := condExpIndL1 hm μ s
  map_add' := condExpIndL1_add
  map_smul' := condExpIndL1_smul
  cont := continuous_condExpIndL1

variable {G}

/--
theorem `condExpInd_ae_eq_condExpIndSMul` / 定理 `condExpInd_ae_eq_condExpIndSMul`

English:
theorem condExpInd_ae_eq_condExpIndSMul
  statement: (hm : m <= m0) [SigmaFinite (μ.trim hm)]
  proof: by
  grw [← condExpIndL1Fin_ae_eq_condExpIndSMul]
  simp [condExpInd, condExpIndL1, hs, hμs]

中文:
定理 condExpInd_ae_eq_condExpIndSMul
  结论: (hm : m <= m0) [SigmaFinite (μ.trim hm)]
  证明: by
  grw [← condExpIndL1Fin_ae_eq_condExpIndSMul]
  simp [condExpInd, condExpIndL1, hs, hμs]

Depends on / 依赖: condExpInd, condExpIndL1, condExpIndL1Fin_ae_eq_condExpIndSMul
-/
theorem condExpInd_ae_eq_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) :
    condExpInd G hm μ s x =ᵐ[μ] condExpIndSMul hm hs hμs x := by
  grw [← condExpIndL1Fin_ae_eq_condExpIndSMul]
  simp [condExpInd, condExpIndL1, hs, hμs]

variable {hm : m <= m0} [SigmaFinite (μ.trim hm)]

/--
theorem `aestronglyMeasurable_condExpInd` / 定理 `aestronglyMeasurable_condExpInd`

English:
theorem aestronglyMeasurable_condExpInd
  given: (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G)
  proof: (aestronglyMeasurable_condExpIndSMul hm hs hμs x).congr
    (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm

@[simp]

中文:
定理 aestronglyMeasurable_condExpInd
  条件: (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G)
  证明: (aestronglyMeasurable_condExpIndSMul hm hs hμs x).congr
    (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm

@[simp]

Depends on / 依赖: aestronglyMeasurable_condExpIndSMul, condExpInd_ae_eq_condExpIndSMul
-/
theorem aestronglyMeasurable_condExpInd (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) :
    AEStronglyMeasurable[m] (condExpInd G hm μ s x) μ :=
  (aestronglyMeasurable_condExpIndSMul hm hs hμs x).congr
    (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm

@[simp]
/--
theorem `condExpInd_empty` / 定理 `condExpInd_empty`

English:
theorem condExpInd_empty
  statement: condExpInd G hm μ ∅ = (0 : G ->L[Real] α ->₁[μ] G)
  proof: by
  ext x
  grw [condExpInd_ae_eq_condExpIndSMul hm MeasurableSet.empty (by simp), condExpIndSMul_empty,
    zero_apply, Lp.coeFn_zero, Lp.coeFn_zero]

中文:
定理 condExpInd_empty
  结论: condExpInd G hm μ ∅ = (0 : G ->L[实数] α ->₁[μ] G)
  证明: by
  ext x
  grw [condExpInd_ae_eq_condExpIndSMul hm MeasurableSet.empty (by simp), condExpIndSMul_empty,
    zero_apply, Lp.coeFn_zero, Lp.coeFn_zero]

Depends on / 依赖: Lp.coeFn_zero, MeasurableSet, MeasurableSet.empty, coeFn_zero, condExpIndSMul_empty, condExpInd_ae_eq_condExpIndSMul, zero_apply
-/
theorem condExpInd_empty : condExpInd G hm μ ∅ = (0 : G ->L[Real] α ->₁[μ] G) := by
  ext x
  grw [condExpInd_ae_eq_condExpIndSMul hm MeasurableSet.empty (by simp), condExpIndSMul_empty,
    zero_apply, Lp.coeFn_zero, Lp.coeFn_zero]

/--
theorem `condExpInd_smul'` / 定理 `condExpInd_smul'`

English:
theorem condExpInd_smul'
  given: [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (c : 𝕜) (x : F)
  proof: condExpIndL1_smul' c x

中文:
定理 condExpInd_smul'
  条件: [NormedSpace 实数 F] [SMulCommClass 实数 𝕜 F] (c : 𝕜) (x : F)
  证明: condExpIndL1_smul' c x

Depends on / 依赖: condExpIndL1_smul
-/
theorem condExpInd_smul' [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (c : 𝕜) (x : F) :
    condExpInd F hm μ s (c • x) = c • condExpInd F hm μ s x :=
  condExpIndL1_smul' c x

/--
theorem `norm_condExpInd_apply_le` / 定理 `norm_condExpInd_apply_le`

English:
theorem norm_condExpInd_apply_le
  given: (x : G)
  statement: ‖condExpInd G hm μ s x‖ <= μ.real s * ‖x‖
  proof: norm_condExpIndL1_le x

中文:
定理 norm_condExpInd_apply_le
  条件: (x : G)
  结论: ‖condExpInd G hm μ s x‖ <= μ.real s * ‖x‖
  证明: norm_condExpIndL1_le x

Depends on / 依赖: norm_condExpIndL1_le
-/
theorem norm_condExpInd_apply_le (x : G) : ‖condExpInd G hm μ s x‖ <= μ.real s * ‖x‖ :=
  norm_condExpIndL1_le x

/--
theorem `norm_condExpInd_le` / 定理 `norm_condExpInd_le`

English:
theorem norm_condExpInd_le
  statement: ‖(condExpInd G hm μ s : G ->L[Real] α ->₁[μ] G)‖ <= μ.real s
  proof: ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg norm_condExpInd_apply_le

中文:
定理 norm_condExpInd_le
  结论: ‖(condExpInd G hm μ s : G ->L[实数] α ->₁[μ] G)‖ <= μ.real s
  证明: ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg norm_condExpInd_apply_le

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, ENNReal, ENNReal.toReal_nonneg, norm_condExpInd_apply_le, opNorm_le_bound, toReal_nonneg
-/
theorem norm_condExpInd_le : ‖(condExpInd G hm μ s : G ->L[Real] α ->₁[μ] G)‖ <= μ.real s :=
  ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg norm_condExpInd_apply_le

/--
theorem `condExpInd_disjoint_union_apply` / 定理 `condExpInd_disjoint_union_apply`

English:
theorem condExpInd_disjoint_union_apply
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: condExpIndL1_disjoint_union hs ht hμs hμt hst x

中文:
定理 condExpInd_disjoint_union_apply
  结论: (hs : MeasurableSet s) (ht : MeasurableSet t)
  证明: condExpIndL1_disjoint_union hs ht hμs hμt hst x

Depends on / 依赖: condExpIndL1_disjoint_union
-/
theorem condExpInd_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s != ∞) (hμt : μ t != ∞) (hst : Disjoint s t) (x : G) :
    condExpInd G hm μ (s union t) x = condExpInd G hm μ s x + condExpInd G hm μ t x :=
  condExpIndL1_disjoint_union hs ht hμs hμt hst x

/--
theorem `condExpInd_disjoint_union` / 定理 `condExpInd_disjoint_union`

English:
theorem condExpInd_disjoint_union
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞)
  proof: by
  ext1 x; push_cast; exact condExpInd_disjoint_union_apply hs ht hμs hμt hst x

中文:
定理 condExpInd_disjoint_union
  结论: (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞)
  证明: by
  ext1 x; push_cast; exact condExpInd_disjoint_union_apply hs ht hμs hμt hst x

Depends on / 依赖: condExpInd_disjoint_union_apply
-/
theorem condExpInd_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞)
    (hμt : μ t != ∞) (hst : Disjoint s t) : (condExpInd G hm μ (s union t) : G ->L[Real] α ->₁[μ] G) =
    condExpInd G hm μ s + condExpInd G hm μ t := by
  ext1 x; push_cast; exact condExpInd_disjoint_union_apply hs ht hμs hμt hst x

variable (G)

/--
theorem `dominatedFinMeasAdditive_condExpInd` / 定理 `dominatedFinMeasAdditive_condExpInd`

English:
theorem dominatedFinMeasAdditive_condExpInd
  statement: (hm : m <= m0) (μ : Measure α)
  proof: ⟨fun _ _ => condExpInd_disjoint_union, fun _ _ _ => norm_condExpInd_le.trans (one_mul _).symm.le⟩

中文:
定理 dominatedFinMeasAdditive_condExpInd
  结论: (hm : m <= m0) (μ : Measure α)
  证明: ⟨fun _ _ => condExpInd_disjoint_union, fun _ _ _ => norm_condExpInd_le.trans (one_mul _).symm.le⟩

Depends on / 依赖: condExpInd_disjoint_union, norm_condExpInd_le, norm_condExpInd_le.trans, one_mul, symm.le
-/
theorem dominatedFinMeasAdditive_condExpInd (hm : m <= m0) (μ : Measure α)
    [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (condExpInd G hm μ : Set α -> G ->L[Real] α ->₁[μ] G) 1 :=
  ⟨fun _ _ => condExpInd_disjoint_union, fun _ _ _ => norm_condExpInd_le.trans (one_mul _).symm.le⟩

variable {G}

/--
theorem `setIntegral_condExpInd` / 定理 `setIntegral_condExpInd`

English:
theorem setIntegral_condExpInd
  statement: (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s != ∞)
  proof: calc
    ∫ a in s, condExpInd G' hm μ t x a ∂μ = ∫ a in s, condExpIndSMul hm ht hμt x a ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpInd_ae_eq_condExpIndSMul hm ht hμt x).mono fun _ hx _ => hx)
    _ = μ.real (t inter s) • x := setIntegral_condExpIndSMul hs ht hμs hμt x

中文:
定理 setIntegral_condExpInd
  结论: (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s != ∞)
  证明: calc
    ∫ a in s, condExpInd G' hm μ t x a ∂μ = ∫ a in s, condExpIndSMul hm ht hμt x a ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpInd_ae_eq_condExpIndSMul hm ht hμt x).mono fun _ hx _ => hx)
    _ = μ.real (t inter s) • x := setIntegral_condExpIndSMul hs ht hμs hμt x

Depends on / 依赖: condExpInd, condExpIndSMul, condExpInd_ae_eq_condExpIndSMul, setIntegral_condExpIndSMul, setIntegral_congr_ae
-/
theorem setIntegral_condExpInd (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s != ∞)
    (hμt : μ t != ∞) (x : G') : ∫ a in s, condExpInd G' hm μ t x a ∂μ = μ.real (t inter s) • x :=
  calc
    ∫ a in s, condExpInd G' hm μ t x a ∂μ = ∫ a in s, condExpIndSMul hm ht hμt x a ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpInd_ae_eq_condExpIndSMul hm ht hμt x).mono fun _ hx _ => hx)
    _ = μ.real (t inter s) • x := setIntegral_condExpIndSMul hs ht hμs hμt x

/--
theorem `condExpInd_of_measurable` / 定理 `condExpInd_of_measurable`

English:
theorem condExpInd_of_measurable
  given: (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (c : G)
  proof: by
  ext1
  grw [indicatorConstLp_coeFn, condExpInd_ae_eq_condExpIndSMul hm (hm s hs) hμs,
    condExpIndSMul_ae_eq_smul]
  rw [condExpL2_indicator_of_measurable hm hs hμs (1 : Real)]
  filter_upwards [@indicatorConstLp_coeFn α _ _ 2 μ _ s (hm s hs) hμs (1 : Real)] with x hx
  rw [hx]
  by_cases hx_

中文:
定理 condExpInd_of_measurable
  条件: (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (c : G)
  证明: by
  ext1
  grw [indicatorConstLp_coeFn, condExpInd_ae_eq_condExpIndSMul hm (hm s hs) hμs,
    condExpIndSMul_ae_eq_smul]
  rw [condExpL2_indicator_of_measurable hm hs hμs (1 : Real)]
  filter_upwards [@indicatorConstLp_coeFn α _ _ 2 μ _ s (hm s hs) hμs (1 : Real)] with x hx
  rw [hx]
  by_cases hx_

Depends on / 依赖: condExpIndSMul_ae_eq_smul, condExpInd_ae_eq_condExpIndSMul, condExpL2_indicator_of_measurable, filter_upwards, hx_mem, indicatorConstLp_coeFn
-/
theorem condExpInd_of_measurable (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (c : G) :
    condExpInd G hm μ s c = indicatorConstLp 1 (hm s hs) hμs c := by
  ext1
  grw [indicatorConstLp_coeFn, condExpInd_ae_eq_condExpIndSMul hm (hm s hs) hμs,
    condExpIndSMul_ae_eq_smul]
  rw [condExpL2_indicator_of_measurable hm hs hμs (1 : Real)]
  filter_upwards [@indicatorConstLp_coeFn α _ _ 2 μ _ s (hm s hs) hμs (1 : Real)] with x hx
  rw [hx]
  by_cases hx_mem : x in s <;> simp [hx_mem]

/--
theorem `condExpInd_nonneg` / 定理 `condExpInd_nonneg`

English:
theorem condExpInd_nonneg
  statement: {E} [NormedAddCommGroup E] [PartialOrder E] [NormedSpace Real E]
  proof: by
  rw [← coeFn_le]
  refine EventuallyLE.trans_eq ?_ (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm
  exact (coeFn_zero E 1 μ).trans_le (condExpIndSMul_nonneg hs hμs x hx)

中文:
定理 condExpInd_nonneg
  结论: {E} [NormedAddCommGroup E] [PartialOrder E] [NormedSpace 实数 E]
  证明: by
  rw [← coeFn_le]
  refine EventuallyLE.trans_eq ?_ (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm
  exact (coeFn_zero E 1 μ).trans_le (condExpIndSMul_nonneg hs hμs x hx)

Depends on / 依赖: EventuallyLE, EventuallyLE.trans_eq, coeFn_le, coeFn_zero, condExpIndSMul_nonneg, condExpInd_ae_eq_condExpIndSMul, trans_eq, trans_le
-/
theorem condExpInd_nonneg {E} [NormedAddCommGroup E] [PartialOrder E] [NormedSpace Real E]
    [IsOrderedModule Real E] (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E) (hx : 0 <= x) :
    0 <= condExpInd E hm μ s x := by
  rw [← coeFn_le]
  refine EventuallyLE.trans_eq ?_ (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm
  exact (coeFn_zero E 1 μ).trans_le (condExpIndSMul_nonneg hs hμs x hx)

end CondexpInd

section CondexpL1


variable {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m <= m0} [SigmaFinite (μ.trim hm)]
  {f g : α -> F'} {s : Set α}

section CondExpL1CLM

variable (F')

/--
Definition of `condExpL1CLM` / `condExpL1CLM` 的定义

English:
definition condExpL1CLM
  signature: (hm : m <= m0) (μ : Measure α) [CompleteSpace ↑(Lp F' 1 μ)]
  body: L1.setToL1 (dominatedFinMeasAdditive_condExpInd F' hm μ)

中文:
定义 condExpL1CLM
  签名: (hm : m <= m0) (μ : Measure α) [CompleteSpace ↑(Lp F' 1 μ)]
  定义体: L1.setToL1 (dominatedFinMeasAdditive_condExpInd F' hm μ)

Depends on / 依赖: L1.setToL1, dominatedFinMeasAdditive_condExpInd, setToL1
-/
def condExpL1CLM (hm : m <= m0) (μ : Measure α) [CompleteSpace ↑(Lp F' 1 μ)]
    [SigmaFinite (μ.trim hm)] :
    (α ->₁[μ] F') ->L[Real] α ->₁[μ] F' :=
  L1.setToL1 (dominatedFinMeasAdditive_condExpInd F' hm μ)

variable {F'}
variable [CompleteSpace F']

/--
theorem `condExpL1CLM_smul` / 定理 `condExpL1CLM_smul`

English:
theorem condExpL1CLM_smul
  given: (c : 𝕜) (f : α ->₁[μ] F')
  proof: by
  refine L1.setToL1_smul (dominatedFinMeasAdditive_condExpInd F' hm μ) ?_ c f
  exact fun c s x => condExpInd_smul' c x

中文:
定理 condExpL1CLM_smul
  条件: (c : 𝕜) (f : α ->₁[μ] F')
  证明: by
  refine L1.setToL1_smul (dominatedFinMeasAdditive_condExpInd F' hm μ) ?_ c f
  exact fun c s x => condExpInd_smul' c x

Depends on / 依赖: L1.setToL1_smul, condExpInd_smul, dominatedFinMeasAdditive_condExpInd, setToL1_smul
-/
theorem condExpL1CLM_smul (c : 𝕜) (f : α ->₁[μ] F') :
    condExpL1CLM F' hm μ (c • f) = c • condExpL1CLM F' hm μ f := by
  refine L1.setToL1_smul (dominatedFinMeasAdditive_condExpInd F' hm μ) ?_ c f
  exact fun c s x => condExpInd_smul' c x

/--
theorem `condExpL1CLM_indicatorConstLp` / 定理 `condExpL1CLM_indicatorConstLp`

English:
theorem condExpL1CLM_indicatorConstLp
  given: (hs : MeasurableSet s) (hμs : μ s != ∞) (x : F')
  proof: L1.setToL1_indicatorConstLp (dominatedFinMeasAdditive_condExpInd F' hm μ) hs hμs x

中文:
定理 condExpL1CLM_indicatorConstLp
  条件: (hs : MeasurableSet s) (hμs : μ s != ∞) (x : F')
  证明: L1.setToL1_indicatorConstLp (dominatedFinMeasAdditive_condExpInd F' hm μ) hs hμs x

Depends on / 依赖: L1.setToL1_indicatorConstLp, dominatedFinMeasAdditive_condExpInd, setToL1_indicatorConstLp
-/
theorem condExpL1CLM_indicatorConstLp (hs : MeasurableSet s) (hμs : μ s != ∞) (x : F') :
    (condExpL1CLM F' hm μ) (indicatorConstLp 1 hs hμs x) = condExpInd F' hm μ s x :=
  L1.setToL1_indicatorConstLp (dominatedFinMeasAdditive_condExpInd F' hm μ) hs hμs x

/--
theorem `condExpL1CLM_indicatorConst` / 定理 `condExpL1CLM_indicatorConst`

English:
theorem condExpL1CLM_indicatorConst
  given: (hs : MeasurableSet s) (hμs : μ s != ∞) (x : F')
  proof: by
  rw [Lp.simpleFunc.coe_indicatorConst]; exact condExpL1CLM_indicatorConstLp hs hμs x

中文:
定理 condExpL1CLM_indicatorConst
  条件: (hs : MeasurableSet s) (hμs : μ s != ∞) (x : F')
  证明: by
  rw [Lp.simpleFunc.coe_indicatorConst]; exact condExpL1CLM_indicatorConstLp hs hμs x

Depends on / 依赖: Lp.simpleFunc.coe_indicatorConst, coe_indicatorConst, condExpL1CLM_indicatorConstLp, simpleFunc
-/
theorem condExpL1CLM_indicatorConst (hs : MeasurableSet s) (hμs : μ s != ∞) (x : F') :
    (condExpL1CLM F' hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condExpInd F' hm μ s x := by
  rw [Lp.simpleFunc.coe_indicatorConst]; exact condExpL1CLM_indicatorConstLp hs hμs x

/--
theorem `setIntegral_condExpL1CLM_of_measure_ne_top` / 定理 `setIntegral_condExpL1CLM_of_measure_ne_top`

English:
theorem setIntegral_condExpL1CLM_of_measure_ne_top
  statement: (f : α ->₁[μ] F') (hs : MeasurableSet[m] s)
  proof: by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α ->₁[μ] F' => ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ) ?_ ?_
    (isClosed_eq ?_ ?_) f
  · intro x t ht hμt
    simp_rw [condExpL1CLM_indicatorConst ht hμt.ne x]
    rw [Lp.simpleFunc.coe_indicatorConst]; rw [s

中文:
定理 setIntegral_condExpL1CLM_of_measure_ne_top
  结论: (f : α ->₁[μ] F') (hs : MeasurableSet[m] s)
  证明: by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α ->₁[μ] F' => ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ) ?_ ?_
    (isClosed_eq ?_ ?_) f
  · intro x t ht hμt
    simp_rw [condExpL1CLM_indicatorConst ht hμt.ne x]
    rw [Lp.simpleFunc.coe_indicatorConst]; rw [s

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, Lp.coeFn_add, Lp.induction, Lp.simpleFunc.coe_indicatorConst, coeFn_add, coe_indicatorConst, condExpL1, condExpL1CLM, condExpL1CLM_indicatorConst, hf_Lp, hg_Lp, isClosed_eq, map_add, one_ne_top, setIntegral_condExpInd, setIntegral_congr_ae, setIntegral_indicatorConstLp, simp_rw, simpleFunc
-/
theorem setIntegral_condExpL1CLM_of_measure_ne_top (f : α ->₁[μ] F') (hs : MeasurableSet[m] s)
    (hμs : μ s != ∞) : ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α ->₁[μ] F' => ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ) ?_ ?_
    (isClosed_eq ?_ ?_) f
  · intro x t ht hμt
    simp_rw [condExpL1CLM_indicatorConst ht hμt.ne x]
    rw [Lp.simpleFunc.coe_indicatorConst]; rw [setIntegral_indicatorConstLp (hm _ hs)]
    exact setIntegral_condExpInd hs ht hμs hμt.ne x
  · intro f g hf_Lp hg_Lp _ hf hg
    simp_rw [(condExpL1CLM F' hm μ).map_add]
    rw [setIntegral_congr_ae (hm s hs) ((Lp.coeFn_add (condExpL1CLM F' hm μ (hf_Lp.toLp f))
      (condExpL1CLM F' hm μ (hg_Lp.toLp g))).mono fun x hx _ => hx)]
    rw [setIntegral_congr_ae (hm s hs)
      ((Lp.coeFn_add (hf_Lp.toLp f) (hg_Lp.toLp g)).mono fun x hx _ => hx)]
    simp_rw [Pi.add_apply]
    rw [integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn]; rw [integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn]; rw [hf]; rw [hg]
  · exact (continuous_setIntegral s).comp (condExpL1CLM F' hm μ).continuous
  · exact continuous_setIntegral s

/--
theorem `setIntegral_condExpL1CLM` / 定理 `setIntegral_condExpL1CLM`

English:
theorem setIntegral_condExpL1CLM
  given: (f : α ->₁[μ] F') (hs : MeasurableSet[m] s)
  proof: by
  let S := spanningSets (μ.trim hm)
  have hS_meas : forall i, MeasurableSet[m] (S i) := measurableSet_spanningSets (μ.trim hm)
  have hS_meas0 : forall i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  have hs_eq : s = ⋃ i, S i inter s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_i

中文:
定理 setIntegral_condExpL1CLM
  条件: (f : α ->₁[μ] F') (hs : MeasurableSet[m] s)
  证明: by
  let S := spanningSets (μ.trim hm)
  have hS_meas : forall i, MeasurableSet[m] (S i) := measurableSet_spanningSets (μ.trim hm)
  have hS_meas0 : forall i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  have hs_eq : s = ⋃ i, S i inter s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_i

Depends on / 依赖: MeasurableSet, Set.inter_comm, Set.inter_iUnion, Set.inter_subset_left, Set.inter_univ, hS_finite, hS_finite_trim, hS_meas, hS_meas0, hs_eq, iUnion_spanningSets, inter_comm, inter_iUnion, inter_subset_left, inter_univ, measurableSet_spanningSets, measure_mono, measure_s, simp_rw, spanningSets
-/
theorem setIntegral_condExpL1CLM (f : α ->₁[μ] F') (hs : MeasurableSet[m] s) :
    ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  let S := spanningSets (μ.trim hm)
  have hS_meas : forall i, MeasurableSet[m] (S i) := measurableSet_spanningSets (μ.trim hm)
  have hS_meas0 : forall i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  have hs_eq : s = ⋃ i, S i inter s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_iUnion]; rw [iUnion_spanningSets (μ.trim hm)]; rw [Set.inter_univ]
  have hS_finite : forall i, μ (S i inter s) < ∞ := by
    refine fun i => (measure_mono Set.inter_subset_left).trans_lt ?_
    have hS_finite_trim := measure_spanningSets_lt_top (μ.trim hm) i
    rwa [trim_measurableSet_eq hm (hS_meas i)] at hS_finite_trim
  have h_mono : Monotone fun i => S i inter s := by
    intro i j hij x
    simp_rw [Set.mem_inter_iff]
    exact fun h => ⟨monotone_spanningSets (μ.trim hm) hij h.1, h.2⟩
  have h_eq_forall :
    (fun i => ∫ x in S i inter s, condExpL1CLM F' hm μ f x ∂μ) = fun i => ∫ x in S i inter s, f x ∂μ :=
    funext fun i =>
      setIntegral_condExpL1CLM_of_measure_ne_top f (@MeasurableSet.inter α m _ _ (hS_meas i) hs)
        (hS_finite i).ne
  have h_right : Tendsto (fun i => ∫ x in S i inter s, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    have h :=
      tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coeFn f).integrableOn
    rwa [← hs_eq] at h
  have h_left : Tendsto (fun i => ∫ x in S i inter s, condExpL1CLM F' hm μ f x ∂μ) atTop
      (𝓝 (∫ x in s, condExpL1CLM F' hm μ f x ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
      (L1.integrable_coeFn (condExpL1CLM F' hm μ f)).integrableOn
    rwa [← hs_eq] at h
  rw [h_eq_forall] at h_left
  exact tendsto_nhds_unique h_left h_right

/--
theorem `aestronglyMeasurable_condExpL1CLM` / 定理 `aestronglyMeasurable_condExpL1CLM`

English:
theorem aestronglyMeasurable_condExpL1CLM
  given: (f : α ->₁[μ] F')
  proof: by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α ->₁[μ] F' => AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [condExpL1CLM_indicatorConst hs hμs.ne c]
    exact aestronglyMeasurable_condExpInd hs hμs.ne c
  · intro f g hf hg _ hfm 

中文:
定理 aestronglyMeasurable_condExpL1CLM
  条件: (f : α ->₁[μ] F')
  证明: by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α ->₁[μ] F' => AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [condExpL1CLM_indicatorConst hs hμs.ne c]
    exact aestronglyMeasurable_condExpInd hs hμs.ne c
  · intro f g hf hg _ hfm 

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.one_ne_top, Lp.induction, aestronglyMeasurable_condExpInd, coeFn_add, condExpL1CLM, condExpL1CLM_indicatorConst, hfm.add, map_add, one_ne_top, s.ne
-/
theorem aestronglyMeasurable_condExpL1CLM (f : α ->₁[μ] F') :
    AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α ->₁[μ] F' => AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [condExpL1CLM_indicatorConst hs hμs.ne c]
    exact aestronglyMeasurable_condExpInd hs hμs.ne c
  · intro f g hf hg _ hfm hgm
    rw [(condExpL1CLM F' hm μ).map_add]
    exact (hfm.add hgm).congr (coeFn_add ..).symm
  · have : {f : Lp F' 1 μ | AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ} =
        condExpL1CLM F' hm μ ⁻¹' {f | AEStronglyMeasurable[m] f μ} := rfl
    rw [this]
    refine IsClosed.preimage (condExpL1CLM F' hm μ).continuous ?_
    exact isClosed_aestronglyMeasurable hm

/--
theorem `condExpL1CLM_lpMeas` / 定理 `condExpL1CLM_lpMeas`

English:
theorem condExpL1CLM_lpMeas
  given: (f : lpMeas F' Real m 1 μ)
  proof: by
  let g := lpMeasToLpTrimLie F' Real 1 μ hm f
  have hfg : f = (lpMeasToLpTrimLie F' Real 1 μ hm).symm g := by
    simp only [g, LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine @Lp.induction α F' m _ 1 (μ.trim hm) _ ENNReal.coe_ne_top (fun g : α ->₁[μ.trim hm] F' =>
    condExpL1CLM F' 

中文:
定理 condExpL1CLM_lpMeas
  条件: (f : lpMeas F' 实数 m 1 μ)
  证明: by
  let g := lpMeasToLpTrimLie F' Real 1 μ hm f
  have hfg : f = (lpMeasToLpTrimLie F' Real 1 μ hm).symm g := by
    simp only [g, LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine @Lp.induction α F' m _ 1 (μ.trim hm) _ ENNReal.coe_ne_top (fun g : α ->₁[μ.trim hm] F' =>
    condExpL1CLM F' 

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, LinearIsometryEquiv, LinearIsometryEquiv.symm_apply_apply, Lp.induction, Lp.simpleFunc.coe_indicatorConst, coe_indicatorConst, coe_ne_top, condExpL1CLM, lpMeasToLpTrimLie, lpMeasToLpTrimLie_symm_in, simpleFunc, symm_apply_apply
-/
theorem condExpL1CLM_lpMeas (f : lpMeas F' Real m 1 μ) :
    condExpL1CLM F' hm μ (f : α ->₁[μ] F') = ↑f := by
  let g := lpMeasToLpTrimLie F' Real 1 μ hm f
  have hfg : f = (lpMeasToLpTrimLie F' Real 1 μ hm).symm g := by
    simp only [g, LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine @Lp.induction α F' m _ 1 (μ.trim hm) _ ENNReal.coe_ne_top (fun g : α ->₁[μ.trim hm] F' =>
    condExpL1CLM F' hm μ ((lpMeasToLpTrimLie F' Real 1 μ hm).symm g : α ->₁[μ] F') =
    ↑((lpMeasToLpTrimLie F' Real 1 μ hm).symm g)) ?_ ?_ ?_ g
  · intro c s hs hμs
    rw [@Lp.simpleFunc.coe_indicatorConst _ _ m]; rw [lpMeasToLpTrimLie_symm_indicator hs hμs.ne c]; rw [condExpL1CLM_indicatorConstLp]
    exact condExpInd_of_measurable hs ((le_trim hm).trans_lt hμs).ne c
  · intro f g hf hg _ hf_eq hg_eq
    rw [LinearIsometryEquiv.map_add]
    push_cast
    rw [map_add]; rw [hf_eq]; rw [hg_eq]
  · refine isClosed_eq ?_ ?_
    · refine (condExpL1CLM F' hm μ).continuous.comp (continuous_induced_dom.comp ?_)
      exact LinearIsometryEquiv.continuous _
    · refine continuous_induced_dom.comp ?_
      exact LinearIsometryEquiv.continuous _

/--
theorem `condExpL1CLM_of_aestronglyMeasurable'` / 定理 `condExpL1CLM_of_aestronglyMeasurable'`

English:
theorem condExpL1CLM_of_aestronglyMeasurable'
  given: (f : α ->₁[μ] F') (hfm : AEStronglyMeasurable[m] f μ)
  proof: condExpL1CLM_lpMeas (⟨f, hfm⟩ : lpMeas F' Real m 1 μ)

中文:
定理 condExpL1CLM_of_aestronglyMeasurable'
  条件: (f : α ->₁[μ] F') (hfm : AEStronglyMeasurable[m] f μ)
  证明: condExpL1CLM_lpMeas (⟨f, hfm⟩ : lpMeas F' Real m 1 μ)

Depends on / 依赖: condExpL1CLM_lpMeas, lpMeas
-/
theorem condExpL1CLM_of_aestronglyMeasurable' (f : α ->₁[μ] F') (hfm : AEStronglyMeasurable[m] f μ) :
    condExpL1CLM F' hm μ f = f :=
  condExpL1CLM_lpMeas (⟨f, hfm⟩ : lpMeas F' Real m 1 μ)

end CondExpL1CLM

set_option linter.overlappingInstances false in
/--
Definition of `condExpL1` / `condExpL1` 的定义

English:
definition condExpL1
  signature: (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
  body: setToFun μ (condExpInd F' hm μ) (dominatedFinMeasAdditive_condExpInd F' hm μ) f

中文:
定义 condExpL1
  签名: (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
  定义体: setToFun μ (condExpInd F' hm μ) (dominatedFinMeasAdditive_condExpInd F' hm μ) f

Depends on / 依赖: condExpInd, dominatedFinMeasAdditive_condExpInd, setToFun
-/
def condExpL1 (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (f : α -> F') : α ->₁[μ] F' :=
  setToFun μ (condExpInd F' hm μ) (dominatedFinMeasAdditive_condExpInd F' hm μ) f

/--
theorem `condExpL1_undef` / 定理 `condExpL1_undef`

English:
theorem condExpL1_undef
  given: (hf : ¬Integrable f μ)
  statement: condExpL1 hm μ f = 0
  proof: setToFun_undef (dominatedFinMeasAdditive_condExpInd F' hm μ) hf

中文:
定理 condExpL1_undef
  条件: (hf : ¬整数egrable f μ)
  结论: condExpL1 hm μ f = 0
  证明: setToFun_undef (dominatedFinMeasAdditive_condExpInd F' hm μ) hf

Depends on / 依赖: dominatedFinMeasAdditive_condExpInd, setToFun_undef
-/
theorem condExpL1_undef (hf : ¬Integrable f μ) : condExpL1 hm μ f = 0 :=
  setToFun_undef (dominatedFinMeasAdditive_condExpInd F' hm μ) hf

/--
theorem `condExpL1_eq` / 定理 `condExpL1_eq`

English:
theorem condExpL1_eq
  statement: [CompleteSpace F']
  proof: setToFun_eq (dominatedFinMeasAdditive_condExpInd F' hm μ) hf

@[simp]

中文:
定理 condExpL1_eq
  结论: [CompleteSpace F']
  证明: setToFun_eq (dominatedFinMeasAdditive_condExpInd F' hm μ) hf

@[simp]

Depends on / 依赖: dominatedFinMeasAdditive_condExpInd, setToFun_eq
-/
theorem condExpL1_eq [CompleteSpace F']
    (hf : Integrable f μ) : condExpL1 hm μ f = condExpL1CLM F' hm μ (hf.toL1 f) :=
  setToFun_eq (dominatedFinMeasAdditive_condExpInd F' hm μ) hf

@[simp]
/--
theorem `condExpL1_zero` / 定理 `condExpL1_zero`

English:
theorem condExpL1_zero
  statement: condExpL1 hm μ (0 : α -> F') = 0
  proof: setToFun_zero _

@[simp]

中文:
定理 condExpL1_zero
  结论: condExpL1 hm μ (0 : α -> F') = 0
  证明: setToFun_zero _

@[simp]

Depends on / 依赖: setToFun_zero
-/
theorem condExpL1_zero : condExpL1 hm μ (0 : α -> F') = 0 :=
  setToFun_zero _

@[simp]
/--
theorem `condExpL1_measure_zero` / 定理 `condExpL1_measure_zero`

English:
theorem condExpL1_measure_zero
  given: (hm : m <= m0)
  statement: condExpL1 hm (0 : Measure α) f = 0
  proof: setToFun_measure_zero _ rfl

中文:
定理 condExpL1_measure_zero
  条件: (hm : m <= m0)
  结论: condExpL1 hm (0 : Measure α) f = 0
  证明: setToFun_measure_zero _ rfl

Depends on / 依赖: setToFun_measure_zero
-/
theorem condExpL1_measure_zero (hm : m <= m0) : condExpL1 hm (0 : Measure α) f = 0 :=
  setToFun_measure_zero _ rfl

/--
theorem `condExpL1_congr_ae` / 定理 `condExpL1_congr_ae`

English:
theorem condExpL1_congr_ae
  given: (hm : m <= m0) (h : f =ᵐ[μ] g)
  proof: setToFun_congr_ae _ h

中文:
定理 condExpL1_congr_ae
  条件: (hm : m <= m0) (h : f =ᵐ[μ] g)
  证明: setToFun_congr_ae _ h

Depends on / 依赖: setToFun_congr_ae
-/
theorem condExpL1_congr_ae (hm : m <= m0) (h : f =ᵐ[μ] g) :
    condExpL1 hm μ f = condExpL1 hm μ g :=
  setToFun_congr_ae _ h

/--
theorem `aestronglyMeasurable_condExpL1` / 定理 `aestronglyMeasurable_condExpL1`

English:
theorem aestronglyMeasurable_condExpL1
  given: {f : α -> F'}
  proof: by
  by_cases hF' : CompleteSpace (Lp F' 1 μ); swap
  · simp only [condExpL1, setToFun, hF', ↓reduceDIte, ZeroMemClass.coe_zero]
    apply stronglyMeasurable_zero.aestronglyMeasurable.congr
    exact (coeFn_zero _ 1 _).symm
  by_cases hf : Integrable f μ; swap
  · rw [condExpL1_undef hf]
    exact s

中文:
定理 aestronglyMeasurable_condExpL1
  条件: {f : α -> F'}
  证明: by
  by_cases hF' : CompleteSpace (Lp F' 1 μ); swap
  · simp only [condExpL1, setToFun, hF', ↓reduceDIte, ZeroMemClass.coe_zero]
    apply stronglyMeasurable_zero.aestronglyMeasurable.congr
    exact (coeFn_zero _ 1 _).symm
  by_cases hf : Integrable f μ; swap
  · rw [condExpL1_undef hf]
    exact s

Depends on / 依赖: CompleteSpace, Integrable, ZeroMemClas, ZeroMemClass, ZeroMemClass.coe_zero, aestronglyMeasurable, coeFn_zero, coe_zero, condExpL1, condExpL1_congr_ae, condExpL1_undef, condExpL1_zero, reduceDIte, setToFun, stronglyMeasurable_zero, stronglyMeasurable_zero.aestronglyMeasurable.congr
-/
theorem aestronglyMeasurable_condExpL1 {f : α -> F'} :
    AEStronglyMeasurable[m] (condExpL1 hm μ f) μ := by
  by_cases hF' : CompleteSpace (Lp F' 1 μ); swap
  · simp only [condExpL1, setToFun, hF', ↓reduceDIte, ZeroMemClass.coe_zero]
    apply stronglyMeasurable_zero.aestronglyMeasurable.congr
    exact (coeFn_zero _ 1 _).symm
  by_cases hf : Integrable f μ; swap
  · rw [condExpL1_undef hf]
    exact stronglyMeasurable_zero.aestronglyMeasurable.congr (coeFn_zero ..).symm
  by_cases hf' : f =ᵐ[μ] 0
  · apply stronglyMeasurable_zero.aestronglyMeasurable.congr
    simp only [condExpL1_congr_ae hm hf', condExpL1_zero, ZeroMemClass.coe_zero]
    exact (coeFn_zero _ 1 _).symm
  have : CompleteSpace F' := by
    have : Nontrivial (Lp F' 1 μ) := by
      apply nontrivial_of_ne (hf.toL1 f) 0
      grw [ne_eq, Lp.ext_iff, Integrable.coeFn_toL1, coeFn_zero]
      exact hf'
    exact completeSpace_of_completeSpace_Lp F' 1 μ
  rw [condExpL1_eq hf]
  exact aestronglyMeasurable_condExpL1CLM _

/--
theorem `integrable_condExpL1` / 定理 `integrable_condExpL1`

English:
theorem integrable_condExpL1
  given: (f : α -> F')
  statement: Integrable (condExpL1 hm μ f) μ
  proof: L1.integrable_coeFn _

中文:
定理 integrable_condExpL1
  条件: (f : α -> F')
  结论: 整数egrable (condExpL1 hm μ f) μ
  证明: L1.integrable_coeFn _

Depends on / 依赖: L1.integrable_coeFn, integrable_coeFn
-/
theorem integrable_condExpL1 (f : α -> F') : Integrable (condExpL1 hm μ f) μ :=
  L1.integrable_coeFn _

/--
theorem `setIntegral_condExpL1` / 定理 `setIntegral_condExpL1`

English:
theorem setIntegral_condExpL1
  given: [CompleteSpace F'] (hf : Integrable f μ) (hs : MeasurableSet[m] s)
  proof: by
  simp_rw [condExpL1_eq hf]
  rw [setIntegral_condExpL1CLM (hf.toL1 f) hs]
  exact setIntegral_congr_ae (hm s hs) (hf.coeFn_toL1.mono fun x hx _ => hx)

中文:
定理 setIntegral_condExpL1
  条件: [CompleteSpace F'] (hf : 整数egrable f μ) (hs : MeasurableSet[m] s)
  证明: by
  simp_rw [condExpL1_eq hf]
  rw [setIntegral_condExpL1CLM (hf.toL1 f) hs]
  exact setIntegral_congr_ae (hm s hs) (hf.coeFn_toL1.mono fun x hx _ => hx)

Depends on / 依赖: coeFn_toL1, condExpL1_eq, hf.coeFn_toL1.mono, hf.toL1, setIntegral_condExpL1CLM, setIntegral_congr_ae, simp_rw
-/
theorem setIntegral_condExpL1 [CompleteSpace F'] (hf : Integrable f μ) (hs : MeasurableSet[m] s) :
    ∫ x in s, condExpL1 hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  simp_rw [condExpL1_eq hf]
  rw [setIntegral_condExpL1CLM (hf.toL1 f) hs]
  exact setIntegral_congr_ae (hm s hs) (hf.coeFn_toL1.mono fun x hx _ => hx)

/--
theorem `condExpL1_add` / 定理 `condExpL1_add`

English:
theorem condExpL1_add
  given: (hf : Integrable f μ) (hg : Integrable g μ)
  proof: setToFun_add _ hf hg

中文:
定理 condExpL1_add
  条件: (hf : 整数egrable f μ) (hg : 整数egrable g μ)
  证明: setToFun_add _ hf hg

Depends on / 依赖: setToFun_add
-/
theorem condExpL1_add (hf : Integrable f μ) (hg : Integrable g μ) :
    condExpL1 hm μ (f + g) = condExpL1 hm μ f + condExpL1 hm μ g :=
  setToFun_add _ hf hg

/--
theorem `condExpL1_neg` / 定理 `condExpL1_neg`

English:
theorem condExpL1_neg
  given: (f : α -> F')
  statement: condExpL1 hm μ (-f) = -condExpL1 hm μ f
  proof: setToFun_neg _ f

中文:
定理 condExpL1_neg
  条件: (f : α -> F')
  结论: condExpL1 hm μ (-f) = -condExpL1 hm μ f
  证明: setToFun_neg _ f

Depends on / 依赖: setToFun_neg
-/
theorem condExpL1_neg (f : α -> F') : condExpL1 hm μ (-f) = -condExpL1 hm μ f :=
  setToFun_neg _ f

/--
theorem `condExpL1_smul` / 定理 `condExpL1_smul`

English:
theorem condExpL1_smul
  given: (c : 𝕜) (f : α -> F')
  statement: condExpL1 hm μ (c • f) = c • condExpL1 hm μ f
  proof: by
  refine setToFun_smul _ ?_ c f
  exact fun c _ x => condExpInd_smul' c x

中文:
定理 condExpL1_smul
  条件: (c : 𝕜) (f : α -> F')
  结论: condExpL1 hm μ (c • f) = c • condExpL1 hm μ f
  证明: by
  refine setToFun_smul _ ?_ c f
  exact fun c _ x => condExpInd_smul' c x

Depends on / 依赖: condExpInd_smul, setToFun_smul
-/
theorem condExpL1_smul (c : 𝕜) (f : α -> F') : condExpL1 hm μ (c • f) = c • condExpL1 hm μ f := by
  refine setToFun_smul _ ?_ c f
  exact fun c _ x => condExpInd_smul' c x

/--
theorem `condExpL1_sub` / 定理 `condExpL1_sub`

English:
theorem condExpL1_sub
  given: (hf : Integrable f μ) (hg : Integrable g μ)
  proof: setToFun_sub _ hf hg

中文:
定理 condExpL1_sub
  条件: (hf : 整数egrable f μ) (hg : 整数egrable g μ)
  证明: setToFun_sub _ hf hg

Depends on / 依赖: setToFun_sub
-/
theorem condExpL1_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    condExpL1 hm μ (f - g) = condExpL1 hm μ f - condExpL1 hm μ g :=
  setToFun_sub _ hf hg

/--
theorem `condExpL1_of_aestronglyMeasurable'` / 定理 `condExpL1_of_aestronglyMeasurable'`

English:
theorem condExpL1_of_aestronglyMeasurable'
  statement: [CompleteSpace F'] (hfm : AEStronglyMeasurable[m] f μ)
  proof: by
  rw [condExpL1_eq hfi]
  refine EventuallyEq.trans ?_ (Integrable.coeFn_toL1 hfi)
  rw [condExpL1CLM_of_aestronglyMeasurable']
  exact hfm.congr hfi.coeFn_toL1.symm

中文:
定理 condExpL1_of_aestronglyMeasurable'
  结论: [CompleteSpace F'] (hfm : AEStronglyMeasurable[m] f μ)
  证明: by
  rw [condExpL1_eq hfi]
  refine EventuallyEq.trans ?_ (Integrable.coeFn_toL1 hfi)
  rw [condExpL1CLM_of_aestronglyMeasurable']
  exact hfm.congr hfi.coeFn_toL1.symm

Depends on / 依赖: EventuallyEq, EventuallyEq.trans, Integrable, Integrable.coeFn_toL1, coeFn_toL1, condExpL1CLM_of_aestronglyMeasurable, condExpL1_eq, hfi.coeFn_toL1.symm, hfm.congr
-/
theorem condExpL1_of_aestronglyMeasurable' [CompleteSpace F'] (hfm : AEStronglyMeasurable[m] f μ)
    (hfi : Integrable f μ) : condExpL1 hm μ f =ᵐ[μ] f := by
  rw [condExpL1_eq hfi]
  refine EventuallyEq.trans ?_ (Integrable.coeFn_toL1 hfi)
  rw [condExpL1CLM_of_aestronglyMeasurable']
  exact hfm.congr hfi.coeFn_toL1.symm

/--
theorem `condExpL1_mono` / 定理 `condExpL1_mono`

English:
theorem condExpL1_mono
  statement: {E}
  proof: by
  rw [coeFn_le]
  have h_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x : E, 0 <= x -> 0 <= condExpInd E hm μ s x :=
    fun s hs hμs x hx => condExpInd_nonneg hs hμs.ne x hx
  exact setToFun_mono (dominatedFinMeasAdditive_condExpInd E hm μ) h_nonneg hf hg hfg

中文:
定理 condExpL1_mono
  结论: {E}
  证明: by
  rw [coeFn_le]
  have h_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x : E, 0 <= x -> 0 <= condExpInd E hm μ s x :=
    fun s hs hμs x hx => condExpInd_nonneg hs hμs.ne x hx
  exact setToFun_mono (dominatedFinMeasAdditive_condExpInd E hm μ) h_nonneg hf hg hfg

Depends on / 依赖: MeasurableSet, coeFn_le, condExpInd, condExpInd_nonneg, dominatedFinMeasAdditive_condExpInd, h_nonneg, s.ne, setToFun_mono
-/
theorem condExpL1_mono {E}
    [NormedAddCommGroup E] [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E]
    [NormedSpace Real E] [IsOrderedModule Real E] {f g : α -> E} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : f <=ᵐ[μ] g) :
    condExpL1 hm μ f <=ᵐ[μ] condExpL1 hm μ g := by
  rw [coeFn_le]
  have h_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x : E, 0 <= x -> 0 <= condExpInd E hm μ s x :=
    fun s hs hμs x hx => condExpInd_nonneg hs hμs.ne x hx
  exact setToFun_mono (dominatedFinMeasAdditive_condExpInd E hm μ) h_nonneg hf hg hfg

end CondexpL1

end MeasureTheory
