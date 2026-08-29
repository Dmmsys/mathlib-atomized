/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Michael Stoll, Terence Tao
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Multiplicative inverse and iteration of real logarithm

We prove properties of the functions `x ↦ (log x)⁻¹` and `x ↦ log (log x)`.

## Main results

- `deriv_inv_log` gives a formula for the derivative of `x ↦ (log x)⁻¹` which holds for all values.
- `deriv_log_log` gives a formula for the derivative of `x ↦ log (log x)` which holds for all
  values.
-/

public section

namespace Real

open Filter Asymptotics Bornology Metric IsOrderBornology DifferentiableAt


/--
lemma `not_differentiableAt_inv_log_zero` / 引理 `not_differentiableAt_inv_log_zero`

English:
lemma not_differentiableAt_inv_log_zero
  statement: ¬ DifferentiableAt Real (fun x => (log x)⁻¹) 0
  proof: by
  simp only [← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope_zero, zero_add, log_zero,
    inv_zero, sub_zero, smul_eq_mul, ← mul_inv, mul_comm _ (log _)]
  refine fun H => (tendsto_nhdsWithin_mono_left (by grind : Set.Iio (0 : Real) subseteq _) H).not_tendsto
    (by simp) (tendsto_inv_nhdsGT_zero.comp ?_)
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_log_mul_self_nhdsLT_zero ?_
  simp only [← nhdsWithin_Ioo_eq_nhdsLT neg_one_lt_zero, Set.mem_Ioi]
  refine eventually_nhdsWithin_of_forall fun x ⟨hx₁, hx₂⟩ => mul_pos_of_neg_of_neg ?_ hx₂
  apply log_neg_eq_log x ▸ log_neg <;> grind

中文:
引理 not_differentiableAt_inv_log_zero
  结论: ¬ DifferentiableAt 实数 (fun x => (log x)⁻¹) 0
  证明: by
  simp only [← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope_zero, zero_add, log_zero,
    inv_zero, sub_zero, smul_eq_mul, ← mul_inv, mul_comm _ (log _)]
  refine fun H => (tendsto_nhdsWithin_mono_left (by grind : Set.Iio (0 : Real) subseteq _) H).not_tendsto
    (by simp) (tendsto_inv_nhdsGT_zero.comp ?_)
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_log_mul_self_nhdsLT_zero ?_
  simp only [← nhdsWithin_Ioo_eq_nhdsLT neg_one_lt_zero, Set.mem_Ioi]
  refine eventually_nhdsWithin_of_forall fun x ⟨hx₁, hx₂⟩ => mul_pos_of_neg_of_neg ?_ hx₂
  apply log_neg_eq_log x ▸ log_neg <;> grind

Depends on / 依赖: Set.Iio, Set.mem_Ioi, eventually_nhdsWith, hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope_zero, inv_zero, log_zero, mem_Ioi, mul_comm, mul_inv, neg_one_lt_zero, nhdsWithin_Ioo_eq_nhdsLT, not_tendsto, smul_eq_mul, sub_zero, subseteq, tendsto_inv_nhdsGT_zero, tendsto_inv_nhdsGT_zero.comp, tendsto_log_mul_self_nhdsLT_zero, tendsto_nhdsWithin_mono_left
-/
lemma not_differentiableAt_inv_log_zero : ¬ DifferentiableAt Real (fun x => (log x)⁻¹) 0 := by
  simp only [← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope_zero, zero_add, log_zero,
    inv_zero, sub_zero, smul_eq_mul, ← mul_inv, mul_comm _ (log _)]
  refine fun H => (tendsto_nhdsWithin_mono_left (by grind : Set.Iio (0 : Real) subseteq _) H).not_tendsto
    (by simp) (tendsto_inv_nhdsGT_zero.comp ?_)
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_log_mul_self_nhdsLT_zero ?_
  simp only [← nhdsWithin_Ioo_eq_nhdsLT neg_one_lt_zero, Set.mem_Ioi]
  refine eventually_nhdsWithin_of_forall fun x ⟨hx₁, hx₂⟩ => mul_pos_of_neg_of_neg ?_ hx₂
  apply log_neg_eq_log x ▸ log_neg <;> grind

/--
lemma `not_continuousAt_inv_log_one` / 引理 `not_continuousAt_inv_log_one`

English:
lemma not_continuousAt_inv_log_one
  statement: ¬ ContinuousAt (fun x => (log x)⁻¹) 1
  proof: by
  suffices Tendsto (fun x => (log x)⁻¹) (nhdsWithin 1 {1}ᶜ) (cobounded Real) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
exact tendsto_inv₀_nhdsNE_zero.comp log_one ▸
    HasDerivAt.tendsto_nhdsNE (by simpa using hasDerivAt_log one_ne_zero) one_ne_zero

中文:
引理 not_continuousAt_inv_log_one
  结论: ¬ ContinuousAt (fun x => (log x)⁻¹) 1
  证明: by
  suffices Tendsto (fun x => (log x)⁻¹) (nhdsWithin 1 {1}ᶜ) (cobounded Real) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
exact tendsto_inv₀_nhdsNE_zero.comp log_one ▸
    HasDerivAt.tendsto_nhdsNE (by simpa using hasDerivAt_log one_ne_zero) one_ne_zero

Depends on / 依赖: HasDerivAt, HasDerivAt.tendsto_nhdsNE, Tendsto, _nhdsNE_zero.comp, cobounded, disjoint_nhds_cobounded, hasDerivAt_log, log_one, nhdsWithin, nhdsWithin_le_nhds, not_continuousAt_of_tendsto, one_ne_zero, tendsto_nhdsNE
-/
lemma not_continuousAt_inv_log_one : ¬ ContinuousAt (fun x => (log x)⁻¹) 1 := by
  suffices Tendsto (fun x => (log x)⁻¹) (nhdsWithin 1 {1}ᶜ) (cobounded Real) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
exact tendsto_inv₀_nhdsNE_zero.comp log_one ▸
    HasDerivAt.tendsto_nhdsNE (by simpa using hasDerivAt_log one_ne_zero) one_ne_zero

/--
lemma `not_continuousAt_inv_log_neg_one` / 引理 `not_continuousAt_inv_log_neg_one`

English:
lemma not_continuousAt_inv_log_neg_one
  statement: ¬ ContinuousAt (fun x => (log x)⁻¹) (-1)
  proof: fun H => not_continuousAt_inv_log_one
    (by simpa only [log_neg_eq_log] using H.comp' continuousAt_neg)

中文:
引理 not_continuousAt_inv_log_neg_one
  结论: ¬ ContinuousAt (fun x => (log x)⁻¹) (-1)
  证明: fun H => not_continuousAt_inv_log_one
    (by simpa only [log_neg_eq_log] using H.comp' continuousAt_neg)

Depends on / 依赖: H.comp, continuousAt_neg, log_neg_eq_log, not_continuousAt_inv_log_one
-/
lemma not_continuousAt_inv_log_neg_one : ¬ ContinuousAt (fun x => (log x)⁻¹) (-1) :=
  fun H => not_continuousAt_inv_log_one
    (by simpa only [log_neg_eq_log] using H.comp' continuousAt_neg)

/--
theorem `deriv_inv_log_apply` / 定理 `deriv_inv_log_apply`

English:
theorem deriv_inv_log_apply
  given: {x : Real}
  statement: deriv (fun x => (log x)⁻¹) x = -x⁻¹ / log x ^ 2
  proof: by
  have := mt (continuousAt (𝕜 := Real)) not_continuousAt_inv_log_neg_one
  have := mt (continuousAt (𝕜 := Real)) not_continuousAt_inv_log_one
  have := not_differentiableAt_inv_log_zero
  obtain (⟨_, _, _⟩ | rfl | rfl | rfl) :
      (x != -1 ∧ x != 0 ∧ x != 1) ∨ x = -1 ∨ x = 0 ∨ x = 1 := by tauto
  · simp_all
  all_goals rw [deriv_zero_of_not_differentiableAt ‹_›]; simp

@[simp]

中文:
定理 deriv_inv_log_apply
  条件: {x : 实数}
  结论: deriv (fun x => (log x)⁻¹) x = -x⁻¹ / log x ^ 2
  证明: by
  have := mt (continuousAt (𝕜 := Real)) not_continuousAt_inv_log_neg_one
  have := mt (continuousAt (𝕜 := Real)) not_continuousAt_inv_log_one
  have := not_differentiableAt_inv_log_zero
  obtain (⟨_, _, _⟩ | rfl | rfl | rfl) :
      (x != -1 ∧ x != 0 ∧ x != 1) ∨ x = -1 ∨ x = 0 ∨ x = 1 := by tauto
  · simp_all
  all_goals rw [deriv_zero_of_not_differentiableAt ‹_›]; simp

@[simp]

Depends on / 依赖: all_goals, continuousAt, deriv_zero_of_not_differentiableAt, not_continuousAt_inv_log_neg_one, not_continuousAt_inv_log_one, not_differentiableAt_inv_log_zero
-/
theorem deriv_inv_log_apply {x : Real} : deriv (fun x => (log x)⁻¹) x = -x⁻¹ / log x ^ 2 := by
  have := mt (continuousAt (𝕜 := Real)) not_continuousAt_inv_log_neg_one
  have := mt (continuousAt (𝕜 := Real)) not_continuousAt_inv_log_one
  have := not_differentiableAt_inv_log_zero
  obtain (⟨_, _, _⟩ | rfl | rfl | rfl) :
      (x != -1 ∧ x != 0 ∧ x != 1) ∨ x = -1 ∨ x = 0 ∨ x = 1 := by tauto
  · simp_all
  all_goals rw [deriv_zero_of_not_differentiableAt ‹_›]; simp

@[simp]
/--
theorem `deriv_inv_log` / 定理 `deriv_inv_log`

English:
theorem deriv_inv_log
  statement: deriv (fun x => (log x)⁻¹) = fun x => -x⁻¹ / log x ^ 2
  proof: funext fun _ => deriv_inv_log_apply

中文:
定理 deriv_inv_log
  结论: deriv (fun x => (log x)⁻¹) = fun x => -x⁻¹ / log x ^ 2
  证明: funext fun _ => deriv_inv_log_apply

Depends on / 依赖: deriv_inv_log_apply
-/
theorem deriv_inv_log : deriv (fun x => (log x)⁻¹) = fun x => -x⁻¹ / log x ^ 2 :=
  funext fun _ => deriv_inv_log_apply

/--
theorem `differentiableAt_inv_log` / 定理 `differentiableAt_inv_log`

English:
theorem differentiableAt_inv_log
  given: {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1)
  proof: by
  fun_prop (disch := grind [log_ne_zero])

中文:
定理 differentiableAt_inv_log
  条件: {x : 实数} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1)
  证明: by
  fun_prop (disch := grind [log_ne_zero])

Depends on / 依赖: fun_prop, log_ne_zero
-/
theorem differentiableAt_inv_log {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1) :
    DifferentiableAt Real (fun x => (log x)⁻¹) x := by
  fun_prop (disch := grind [log_ne_zero])

/--
theorem `hasDerivAt_inv_log` / 定理 `hasDerivAt_inv_log`

English:
theorem hasDerivAt_inv_log
  given: {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1)
  proof: by
  simpa using (differentiableAt_inv_log hx₀ hx₁ hx₂).hasDerivAt

中文:
定理 hasDerivAt_inv_log
  条件: {x : 实数} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1)
  证明: by
  simpa using (differentiableAt_inv_log hx₀ hx₁ hx₂).hasDerivAt

Depends on / 依赖: differentiableAt_inv_log, hasDerivAt
-/
theorem hasDerivAt_inv_log {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1) :
    HasDerivAt (fun x => (log x)⁻¹) (-x⁻¹ / (log x ^ 2)) x := by
  simpa using (differentiableAt_inv_log hx₀ hx₁ hx₂).hasDerivAt

/--
theorem `differentiableOn_inv_log'` / 定理 `differentiableOn_inv_log'`

English:
theorem differentiableOn_inv_log'
  statement: DifferentiableOn Real (fun x => (log x)⁻¹) {-1,0,1}ᶜ
  proof: (differentiableOn_log.mono (by grind)).inv (by simp; tauto)

中文:
定理 differentiableOn_inv_log'
  结论: DifferentiableOn 实数 (fun x => (log x)⁻¹) {-1,0,1}ᶜ
  证明: (differentiableOn_log.mono (by grind)).inv (by simp; tauto)

Depends on / 依赖: differentiableOn_log, differentiableOn_log.mono
-/
theorem differentiableOn_inv_log' : DifferentiableOn Real (fun x => (log x)⁻¹) {-1,0,1}ᶜ :=
  (differentiableOn_log.mono (by grind)).inv (by simp; tauto)

/--
theorem `differentiableOn_inv_log` / 定理 `differentiableOn_inv_log`

English:
theorem differentiableOn_inv_log
  statement: DifferentiableOn Real (fun x => (log x)⁻¹) (.Ioi 1)
  proof: differentiableOn_inv_log'.mono (by grind)

中文:
定理 differentiableOn_inv_log
  结论: DifferentiableOn 实数 (fun x => (log x)⁻¹) (.左开右无界区间 1)
  证明: differentiableOn_inv_log'.mono (by grind)

Depends on / 依赖: differentiableOn_inv_log
-/
theorem differentiableOn_inv_log : DifferentiableOn Real (fun x => (log x)⁻¹) (.Ioi 1) :=
  differentiableOn_inv_log'.mono (by grind)

/--
theorem `inv_log_isLittleO_one` / 定理 `inv_log_isLittleO_one`

English:
theorem inv_log_isLittleO_one
  statement: (fun x => (log x)⁻¹) =o[atTop] fun _ => (1 : Real)
  proof: by
  rw [isLittleO_one_iff]
  convert tendsto_log_atTop.inv_tendsto_atTop; simp

中文:
定理 inv_log_isLittleO_one
  结论: (fun x => (log x)⁻¹) =o[atTop] fun _ => (1 : 实数)
  证明: by
  rw [isLittleO_one_iff]
  convert tendsto_log_atTop.inv_tendsto_atTop; simp

Depends on / 依赖: convert, inv_tendsto_atTop, isLittleO_one_iff, tendsto_log_atTop, tendsto_log_atTop.inv_tendsto_atTop
-/
theorem inv_log_isLittleO_one : (fun x => (log x)⁻¹) =o[atTop] fun _ => (1 : Real) := by
  rw [isLittleO_one_iff]
  convert tendsto_log_atTop.inv_tendsto_atTop; simp


/--
lemma `not_continuousAt_log_log_zero` / 引理 `not_continuousAt_log_log_zero`

English:
lemma not_continuousAt_log_log_zero
  statement: ¬ ContinuousAt (fun x => log (log x)) 0
  proof: by
  suffices Tendsto (fun x => log (log x)) (nhdsWithin 0 {0}ᶜ) (cobounded Real) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
  have : Tendsto log atBot atTop := by
    convert tendsto_log_atTop.comp tendsto_neg_atBot_atTop; ext; simp
  exact (this.mono_right atTop_le_cobounded).comp tendsto_log_nhdsNE_zero

中文:
引理 not_continuousAt_log_log_zero
  结论: ¬ ContinuousAt (fun x => log (log x)) 0
  证明: by
  suffices Tendsto (fun x => log (log x)) (nhdsWithin 0 {0}ᶜ) (cobounded Real) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
  have : Tendsto log atBot atTop := by
    convert tendsto_log_atTop.comp tendsto_neg_atBot_atTop; ext; simp
  exact (this.mono_right atTop_le_cobounded).comp tendsto_log_nhdsNE_zero

Depends on / 依赖: Tendsto, atTop_le_cobounded, cobounded, convert, disjoint_nhds_cobounded, mono_right, nhdsWithin, nhdsWithin_le_nhds, not_continuousAt_of_tendsto, tendsto_log_atTop, tendsto_log_atTop.comp, tendsto_log_nhdsNE_zero, tendsto_neg_atBot_atTop, this.mono_right
-/
lemma not_continuousAt_log_log_zero : ¬ ContinuousAt (fun x => log (log x)) 0 := by
  suffices Tendsto (fun x => log (log x)) (nhdsWithin 0 {0}ᶜ) (cobounded Real) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
  have : Tendsto log atBot atTop := by
    convert tendsto_log_atTop.comp tendsto_neg_atBot_atTop; ext; simp
  exact (this.mono_right atTop_le_cobounded).comp tendsto_log_nhdsNE_zero

/--
lemma `not_continuousAt_log_log_one` / 引理 `not_continuousAt_log_log_one`

English:
lemma not_continuousAt_log_log_one
  statement: ¬ ContinuousAt (fun x => log (log x)) 1
  proof: by
  suffices Tendsto (fun x => log (log x)) (nhdsWithin 1 {1}ᶜ) (cobounded Real) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
exact (tendsto_log_nhdsNE_zero.mono_right atBot_le_cobounded).comp log_one ▸
    HasDerivAt.tendsto_nhdsNE (by simpa using hasDerivAt_log one_ne_zero) one_ne_zero

中文:
引理 not_continuousAt_log_log_one
  结论: ¬ ContinuousAt (fun x => log (log x)) 1
  证明: by
  suffices Tendsto (fun x => log (log x)) (nhdsWithin 1 {1}ᶜ) (cobounded Real) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
exact (tendsto_log_nhdsNE_zero.mono_right atBot_le_cobounded).comp log_one ▸
    HasDerivAt.tendsto_nhdsNE (by simpa using hasDerivAt_log one_ne_zero) one_ne_zero

Depends on / 依赖: HasDerivAt, HasDerivAt.tendsto_nhdsNE, Tendsto, atBot_le_cobounded, cobounded, disjoint_nhds_cobounded, hasDerivAt_log, log_one, mono_right, nhdsWithin, nhdsWithin_le_nhds, not_continuousAt_of_tendsto, one_ne_zero, tendsto_log_nhdsNE_zero, tendsto_log_nhdsNE_zero.mono_right, tendsto_nhdsNE
-/
lemma not_continuousAt_log_log_one : ¬ ContinuousAt (fun x => log (log x)) 1 := by
  suffices Tendsto (fun x => log (log x)) (nhdsWithin 1 {1}ᶜ) (cobounded Real) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (disjoint_nhds_cobounded _)
exact (tendsto_log_nhdsNE_zero.mono_right atBot_le_cobounded).comp log_one ▸
    HasDerivAt.tendsto_nhdsNE (by simpa using hasDerivAt_log one_ne_zero) one_ne_zero

/--
lemma `not_continuousAt_log_log_neg_one` / 引理 `not_continuousAt_log_log_neg_one`

English:
lemma not_continuousAt_log_log_neg_one
  statement: ¬ ContinuousAt (fun x => log (log x)) (-1)
  proof: fun H => not_continuousAt_log_log_one
    (by simpa only [log_neg_eq_log] using H.comp' continuousAt_neg)

中文:
引理 not_continuousAt_log_log_neg_one
  结论: ¬ ContinuousAt (fun x => log (log x)) (-1)
  证明: fun H => not_continuousAt_log_log_one
    (by simpa only [log_neg_eq_log] using H.comp' continuousAt_neg)

Depends on / 依赖: H.comp, continuousAt_neg, log_neg_eq_log, not_continuousAt_log_log_one
-/
lemma not_continuousAt_log_log_neg_one : ¬ ContinuousAt (fun x => log (log x)) (-1) :=
  fun H => not_continuousAt_log_log_one
    (by simpa only [log_neg_eq_log] using H.comp' continuousAt_neg)

/--
theorem `deriv_log_log_apply` / 定理 `deriv_log_log_apply`

English:
theorem deriv_log_log_apply
  given: {x : Real}
  statement: deriv (fun x => log (log x)) x = x⁻¹ / log x
  proof: by
  have := not_continuousAt_log_log_neg_one
  have := not_continuousAt_log_log_zero
  have := not_continuousAt_log_log_one
  obtain (⟨_, _, _⟩ | rfl | rfl | rfl) :
      (x != -1 ∧ x != 0 ∧ x != 1) ∨ x = -1 ∨ x = 0 ∨ x = 1 := by tauto
  · simp_all
  all_goals rw [deriv_zero_of_not_differentiableAt (mt continuousAt ‹_›)]; simp

@[simp]

中文:
定理 deriv_log_log_apply
  条件: {x : 实数}
  结论: deriv (fun x => log (log x)) x = x⁻¹ / log x
  证明: by
  have := not_continuousAt_log_log_neg_one
  have := not_continuousAt_log_log_zero
  have := not_continuousAt_log_log_one
  obtain (⟨_, _, _⟩ | rfl | rfl | rfl) :
      (x != -1 ∧ x != 0 ∧ x != 1) ∨ x = -1 ∨ x = 0 ∨ x = 1 := by tauto
  · simp_all
  all_goals rw [deriv_zero_of_not_differentiableAt (mt continuousAt ‹_›)]; simp

@[simp]

Depends on / 依赖: all_goals, continuousAt, deriv_zero_of_not_differentiableAt, not_continuousAt_log_log_neg_one, not_continuousAt_log_log_one, not_continuousAt_log_log_zero
-/
theorem deriv_log_log_apply {x : Real} : deriv (fun x => log (log x)) x = x⁻¹ / log x := by
  have := not_continuousAt_log_log_neg_one
  have := not_continuousAt_log_log_zero
  have := not_continuousAt_log_log_one
  obtain (⟨_, _, _⟩ | rfl | rfl | rfl) :
      (x != -1 ∧ x != 0 ∧ x != 1) ∨ x = -1 ∨ x = 0 ∨ x = 1 := by tauto
  · simp_all
  all_goals rw [deriv_zero_of_not_differentiableAt (mt continuousAt ‹_›)]; simp

@[simp]
/--
theorem `deriv_log_log` / 定理 `deriv_log_log`

English:
theorem deriv_log_log
  statement: deriv (fun x => log (log x)) = fun x => x⁻¹ / log x
  proof: funext fun _ => deriv_log_log_apply

中文:
定理 deriv_log_log
  结论: deriv (fun x => log (log x)) = fun x => x⁻¹ / log x
  证明: funext fun _ => deriv_log_log_apply

Depends on / 依赖: deriv_log_log_apply
-/
theorem deriv_log_log : deriv (fun x => log (log x)) = fun x => x⁻¹ / log x :=
  funext fun _ => deriv_log_log_apply

/--
theorem `differentiableAt_log_log` / 定理 `differentiableAt_log_log`

English:
theorem differentiableAt_log_log
  given: {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1)
  proof: (differentiableAt_log (by grind)).log (by simp; grind)

中文:
定理 differentiableAt_log_log
  条件: {x : 实数} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1)
  证明: (differentiableAt_log (by grind)).log (by simp; grind)

Depends on / 依赖: differentiableAt_log
-/
theorem differentiableAt_log_log {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1) :
    DifferentiableAt Real (fun x => log (log x)) x :=
  (differentiableAt_log (by grind)).log (by simp; grind)

/--
theorem `hasDerivAt_log_log` / 定理 `hasDerivAt_log_log`

English:
theorem hasDerivAt_log_log
  given: {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1)
  proof: by
  simpa using (differentiableAt_log_log hx₀ hx₁ hx₂).hasDerivAt

中文:
定理 hasDerivAt_log_log
  条件: {x : 实数} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1)
  证明: by
  simpa using (differentiableAt_log_log hx₀ hx₁ hx₂).hasDerivAt

Depends on / 依赖: differentiableAt_log_log, hasDerivAt
-/
theorem hasDerivAt_log_log {x : Real} (hx₀ : x != 0) (hx₁ : x != 1) (hx₂ : x != -1) :
    HasDerivAt (fun x => log (log x)) (x⁻¹ / log x) x := by
  simpa using (differentiableAt_log_log hx₀ hx₁ hx₂).hasDerivAt

/--
theorem `differentiableOn_log_log'` / 定理 `differentiableOn_log_log'`

English:
theorem differentiableOn_log_log'
  statement: DifferentiableOn Real (fun x => log (log x)) {-1,0,1}ᶜ
  proof: (differentiableOn_log.mono (by grind)).log (by simp; tauto)

中文:
定理 differentiableOn_log_log'
  结论: DifferentiableOn 实数 (fun x => log (log x)) {-1,0,1}ᶜ
  证明: (differentiableOn_log.mono (by grind)).log (by simp; tauto)

Depends on / 依赖: differentiableOn_log, differentiableOn_log.mono
-/
theorem differentiableOn_log_log' : DifferentiableOn Real (fun x => log (log x)) {-1,0,1}ᶜ :=
  (differentiableOn_log.mono (by grind)).log (by simp; tauto)

/--
theorem `differentiableOn_log_log` / 定理 `differentiableOn_log_log`

English:
theorem differentiableOn_log_log
  statement: DifferentiableOn Real (fun x => log (log x)) (.Ioi 1)
  proof: differentiableOn_log_log'.mono (by grind)

中文:
定理 differentiableOn_log_log
  结论: DifferentiableOn 实数 (fun x => log (log x)) (.左开右无界区间 1)
  证明: differentiableOn_log_log'.mono (by grind)

Depends on / 依赖: differentiableOn_log_log
-/
theorem differentiableOn_log_log : DifferentiableOn Real (fun x => log (log x)) (.Ioi 1) :=
  differentiableOn_log_log'.mono (by grind)

/--
theorem `one_isLittleO_log_log` / 定理 `one_isLittleO_log_log`

English:
theorem one_isLittleO_log_log
  statement: (fun _ => (1 : Real)) =o[atTop] fun x => log (log x)
  proof: by
  simp only [isLittleO_one_left_iff, norm_eq_abs]
  exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

中文:
定理 one_isLittleO_log_log
  结论: (fun _ => (1 : 实数)) =o[atTop] fun x => log (log x)
  证明: by
  simp only [isLittleO_one_left_iff, norm_eq_abs]
  exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

Depends on / 依赖: isLittleO_one_left_iff, norm_eq_abs, tendsto_abs_atTop_atTop, tendsto_abs_atTop_atTop.comp, tendsto_log_atTop, tendsto_log_atTop.comp
-/
theorem one_isLittleO_log_log : (fun _ => (1 : Real)) =o[atTop] fun x => log (log x) := by
  simp only [isLittleO_one_left_iff, norm_eq_abs]
  exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real
