/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.MeasureTheory.Integral.CircleAverage


/-!
# The Proximity Function of Value Distribution Theory

This file defines the "proximity function" attached to a meromorphic function defined on the complex
plane. Also known as the `Nevanlinna Proximity Function`, this is one of the three main functions
used in Value Distribution Theory.

The proximity function is a logarithmically weighted measure quantifying how well a meromorphic
function `f` approximates the constant function `a` on the circle of radius `R` in the complex
plane. The definition ensures that large values correspond to good approximation.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

@[expose] public section

open Filter Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E]
  {f g : Complex -> E} {a : WithTop E} {a₀ : E}

open Real

variable (f a) in
/--
Definition of `proximity` / `proximity` 的定义

English:
definition proximity
  signature: : Real -> Real
  body: by
  by_cases h : a = ⊤
  · exact circleAverage (log⁺ ‖f ·‖) 0
  · exact circleAverage (log⁺ ‖f · - a.untop₀‖⁻¹) 0

中文:
定义 proximity
  签名: : 实数 -> 实数
  定义体: by
  by_cases h : a = ⊤
  · exact circleAverage (log⁺ ‖f ·‖) 0
  · exact circleAverage (log⁺ ‖f · - a.untop₀‖⁻¹) 0

Depends on / 依赖: a.untop, circleAverage
-/
noncomputable def proximity : Real -> Real := by
  by_cases h : a = ⊤
  · exact circleAverage (log⁺ ‖f ·‖) 0
  · exact circleAverage (log⁺ ‖f · - a.untop₀‖⁻¹) 0

/--
lemma `proximity_coe` / 引理 `proximity_coe`

English:
lemma proximity_coe
  proof: by
  simp [proximity]

中文:
引理 proximity_coe
  证明: by
  simp [proximity]

Depends on / 依赖: proximity
-/
lemma proximity_coe :
    proximity f a₀ = circleAverage (log⁺ ‖f · - a₀‖⁻¹) 0 := by
  simp [proximity]

/--
lemma `proximity_zero` / 引理 `proximity_zero`

English:
lemma proximity_zero
  statement: proximity f 0 = circleAverage (log⁺ ‖f ·‖⁻¹) 0
  proof: by
  simp [proximity]

中文:
引理 proximity_zero
  结论: proximity f 0 = circleAverage (log⁺ ‖f ·‖⁻¹) 0
  证明: by
  simp [proximity]

Depends on / 依赖: proximity
-/
lemma proximity_zero : proximity f 0 = circleAverage (log⁺ ‖f ·‖⁻¹) 0 := by
  simp [proximity]

/--
lemma `proximity_zero_of_complexValued` / 引理 `proximity_zero_of_complexValued`

English:
lemma proximity_zero_of_complexValued
  given: {f : Complex -> Complex}
  proof: by
  simp [proximity]

中文:
引理 proximity_zero_of_complexValued
  条件: {f : 复形 -> 复形}
  证明: by
  simp [proximity]

Depends on / 依赖: proximity
-/
lemma proximity_zero_of_complexValued {f : Complex -> Complex} :
    proximity f 0 = circleAverage (log⁺ ‖f⁻¹ ·‖) 0 := by
  simp [proximity]

/--
lemma `proximity_top` / 引理 `proximity_top`

English:
lemma proximity_top
  statement: proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0
  proof: by
  simp [proximity]

中文:
引理 proximity_top
  结论: proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0
  证明: by
  simp [proximity]

Depends on / 依赖: proximity
-/
lemma proximity_top : proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0 := by
  simp [proximity]

/-!
## Elementary Properties of the Proximity Function
-/

/--
lemma `proximity_congr_codiscreteWithin` / 引理 `proximity_congr_codiscreteWithin`

English:
lemma proximity_congr_codiscreteWithin
  statement: {f g : Complex -> E} {a : WithTop E} {r : Real}
  proof: by
  by_cases h : a = ⊤
  all_goals
    simp only [proximity, h, ↓reduceDIte]
    apply circleAverage_congr_codiscreteWithin _ hr
    filter_upwards [hfg] using by aesop

中文:
引理 proximity_congr_codiscreteWithin
  结论: {f g : 复形 -> E} {a : WithTop E} {r : 实数}
  证明: by
  by_cases h : a = ⊤
  all_goals
    simp only [proximity, h, ↓reduceDIte]
    apply circleAverage_congr_codiscreteWithin _ hr
    filter_upwards [hfg] using by aesop

Depends on / 依赖: all_goals, circleAverage_congr_codiscreteWithin, filter_upwards, proximity, reduceDIte
-/
lemma proximity_congr_codiscreteWithin {f g : Complex -> E} {a : WithTop E} {r : Real}
    (hfg : f =ᶠ[codiscreteWithin (sphere 0 |r|)] g) (hr : r != 0) :
    proximity f a r = proximity g a r := by
  by_cases h : a = ⊤
  all_goals
    simp only [proximity, h, ↓reduceDIte]
    apply circleAverage_congr_codiscreteWithin _ hr
    filter_upwards [hfg] using by aesop

/--
lemma `proximity_congr_codiscrete` / 引理 `proximity_congr_codiscrete`

English:
lemma proximity_congr_codiscrete
  statement: {f g : Complex -> E} {a : WithTop E} {r : Real}
  proof: proximity_congr_codiscreteWithin (hfg.filter_mono (codiscreteWithin_mono (by tauto))) hr

中文:
引理 proximity_congr_codiscrete
  结论: {f g : 复形 -> E} {a : WithTop E} {r : 实数}
  证明: proximity_congr_codiscreteWithin (hfg.filter_mono (codiscreteWithin_mono (by tauto))) hr

Depends on / 依赖: codiscreteWithin_mono, filter_mono, hfg.filter_mono, proximity_congr_codiscreteWithin
-/
lemma proximity_congr_codiscrete {f g : Complex -> E} {a : WithTop E} {r : Real}
    (hfg : f =ᶠ[codiscrete Complex] g) (hr : r != 0) :
    proximity f a r = proximity g a r :=
  proximity_congr_codiscreteWithin (hfg.filter_mono (codiscreteWithin_mono (by tauto))) hr

/--
lemma `proximity_coe_eq_proximity_sub_const_zero` / 引理 `proximity_coe_eq_proximity_sub_const_zero`

English:
lemma proximity_coe_eq_proximity_sub_const_zero
  proof: by
  simp [proximity]

中文:
引理 proximity_coe_eq_proximity_sub_const_zero
  证明: by
  simp [proximity]

Depends on / 依赖: proximity
-/
lemma proximity_coe_eq_proximity_sub_const_zero :
    proximity f a₀ = proximity (f - fun _ => a₀) 0 := by
  simp [proximity]

/--
theorem `proximity_inv` / 定理 `proximity_inv`

English:
theorem proximity_inv
  given: {f : Complex -> Complex}
  statement: proximity f⁻¹ ⊤ = proximity f 0
  proof: by
  simp [proximity_zero, proximity_top]

中文:
定理 proximity_inv
  条件: {f : 复形 -> 复形}
  结论: proximity f⁻¹ ⊤ = proximity f 0
  证明: by
  simp [proximity_zero, proximity_top]

Depends on / 依赖: proximity_top, proximity_zero
-/
theorem proximity_inv {f : Complex -> Complex} : proximity f⁻¹ ⊤ = proximity f 0 := by
  simp [proximity_zero, proximity_top]

/--
theorem `proximity_sub_proximity_inv_eq_circleAverage` / 定理 `proximity_sub_proximity_inv_eq_circleAverage`

English:
theorem proximity_sub_proximity_inv_eq_circleAverage
  given: {f : Complex -> Complex} (h₁f : Meromorphic f)
  proof: by
  ext R
  simp only [proximity, ↓reduceDIte, Pi.inv_apply, norm_inv, Pi.sub_apply]
  rw [← circleAverage_sub]
  · simp_rw [← posLog_sub_posLog_inv, Pi.sub_def]
  · apply h₁f.meromorphicOn.circleIntegrable_posLog_norm
  · simp_rw [← norm_inv]
    apply h₁f.inv.meromorphicOn.circleIntegrable_posLog

中文:
定理 proximity_sub_proximity_inv_eq_circleAverage
  条件: {f : 复形 -> 复形} (h₁f : 亚纯 f)
  证明: by
  ext R
  simp only [proximity, ↓reduceDIte, Pi.inv_apply, norm_inv, Pi.sub_apply]
  rw [← circleAverage_sub]
  · simp_rw [← posLog_sub_posLog_inv, Pi.sub_def]
  · apply h₁f.meromorphicOn.circleIntegrable_posLog_norm
  · simp_rw [← norm_inv]
    apply h₁f.inv.meromorphicOn.circleIntegrable_posLog

Depends on / 依赖: Pi.inv_apply, Pi.sub_apply, Pi.sub_def, circleAverage_sub, circleIntegrable_posLog_norm, f.inv.meromorphicOn.circleIntegrable_posLog_norm, f.meromorphicOn.circleIntegrable_posLog_norm, inv_apply, meromorphicOn, norm_inv, posLog_sub_posLog_inv, proximity, reduceDIte, simp_rw, sub_apply, sub_def
-/
theorem proximity_sub_proximity_inv_eq_circleAverage {f : Complex -> Complex} (h₁f : Meromorphic f) :
    proximity f ⊤ - proximity f⁻¹ ⊤ = circleAverage (log ‖f ·‖) 0 := by
  ext R
  simp only [proximity, ↓reduceDIte, Pi.inv_apply, norm_inv, Pi.sub_apply]
  rw [← circleAverage_sub]
  · simp_rw [← posLog_sub_posLog_inv, Pi.sub_def]
  · apply h₁f.meromorphicOn.circleIntegrable_posLog_norm
  · simp_rw [← norm_inv]
    apply h₁f.inv.meromorphicOn.circleIntegrable_posLog_norm

/--
theorem `proximity_even` / 定理 `proximity_even`

English:
theorem proximity_even
  statement: (proximity f a).Even
  proof: by
  intro r
  by_cases h : a = ⊤ <;> simp [proximity, h]

中文:
定理 proximity_even
  结论: (proximity f a).Even
  证明: by
  intro r
  by_cases h : a = ⊤ <;> simp [proximity, h]

Depends on / 依赖: proximity
-/
theorem proximity_even : (proximity f a).Even := by
  intro r
  by_cases h : a = ⊤ <;> simp [proximity, h]

/--
theorem `proximity_nonneg` / 定理 `proximity_nonneg`

English:
theorem proximity_nonneg
  given: {a : WithTop E}
  proof: by
  by_cases h : a = ⊤ <;>
  · intro r
    simpa [proximity, h] using circleAverage_nonneg_of_nonneg (fun x _ => posLog_nonneg)

中文:
定理 proximity_nonneg
  条件: {a : WithTop E}
  证明: by
  by_cases h : a = ⊤ <;>
  · intro r
    simpa [proximity, h] using circleAverage_nonneg_of_nonneg (fun x _ => posLog_nonneg)

Depends on / 依赖: circleAverage_nonneg_of_nonneg, posLog_nonneg, proximity
-/
theorem proximity_nonneg {a : WithTop E} :
    0 <= proximity f a := by
  by_cases h : a = ⊤ <;>
  · intro r
    simpa [proximity, h] using circleAverage_nonneg_of_nonneg (fun x _ => posLog_nonneg)

/--
lemma `proximity_const` / 引理 `proximity_const`

English:
lemma proximity_const
  given: {c : E} {r : Real}
  proof: by
  simp [proximity, circleAverage_const]

中文:
引理 proximity_const
  条件: {c : E} {r : 实数}
  证明: by
  simp [proximity, circleAverage_const]
-/
@[simp] lemma proximity_const {c : E} {r : Real} :
    proximity (fun _ => c) ⊤ r = log⁺ ‖c‖ := by
  simp [proximity, circleAverage_const]

/--
theorem `continuous_proximity_top` / 定理 `continuous_proximity_top`

English:
theorem continuous_proximity_top
  given: (hf : Continuous f)
  proof: by
  simp only [proximity, reduceDIte]
  fun_prop

中文:
定理 continuous_proximity_top
  条件: (hf : 连续 f)
  证明: by
  simp only [proximity, reduceDIte]
  fun_prop
-/
@[fun_prop] theorem continuous_proximity_top (hf : Continuous f) :
    Continuous (proximity f ⊤) := by
  simp only [proximity, reduceDIte]
  fun_prop

/-!
## Behaviour under Arithmetic Operations
-/

/--
theorem `proximity_sum_top_le` / 定理 `proximity_sum_top_le`

English:
theorem proximity_sum_top_le
  statement: [NormedSpace Complex E] {α : Type*} (s : Finset α) (f : α -> Complex -> E)
  proof: by
  simp only [proximity_top, Finset.sum_apply]
  intro r
  have h₂f : forall i in s, CircleIntegrable (log⁺ ‖f i ·‖) 0 r :=
    fun i hi => MeromorphicOn.circleIntegrable_posLog_norm (fun x hx => hf i hi x)
  simp only [Pi.add_apply, Finset.sum_apply]
  calc circleAverage (log⁺ ‖∑ c in s, f c ·‖) 

中文:
定理 proximity_sum_top_le
  结论: [赋范空间 复形 E] {α : 类型} (s : 有限集 α) (f : α -> 复形 -> E)
  证明: by
  simp only [proximity_top, Finset.sum_apply]
  intro r
  have h₂f : forall i in s, CircleIntegrable (log⁺ ‖f i ·‖) 0 r :=
    fun i hi => MeromorphicOn.circleIntegrable_posLog_norm (fun x hx => hf i hi x)
  simp only [Pi.add_apply, Finset.sum_apply]
  calc circleAverage (log⁺ ‖∑ c in s, f c ·‖) 

Depends on / 依赖: CircleIntegrable, Finset, Finset.sum_apply, Meromorphic, Meromorphic.fun_sum, MeromorphicOn, MeromorphicOn.circleIntegrable_posLog_norm, Pi.add_apply, add_apply, add_comm, circleAverage, circleAverage_mono, circleIntegrable_posLog_norm, fun_prop, fun_sum, meromorphicOn, meromorphicOn.circleIntegrable_posLog_norm, proximity_top, s.card, sum_apply
-/
theorem proximity_sum_top_le [NormedSpace Complex E] {α : Type*} (s : Finset α) (f : α -> Complex -> E)
    (hf : forall a in s, Meromorphic (f a)) :
    proximity (∑ a in s, f a) ⊤ <= ∑ a in s, (proximity (f a) ⊤) + (fun _ => log s.card) := by
  simp only [proximity_top, Finset.sum_apply]
  intro r
  have h₂f : forall i in s, CircleIntegrable (log⁺ ‖f i ·‖) 0 r :=
    fun i hi => MeromorphicOn.circleIntegrable_posLog_norm (fun x hx => hf i hi x)
  simp only [Pi.add_apply, Finset.sum_apply]
  calc circleAverage (log⁺ ‖∑ c in s, f c ·‖) 0 r
    _ <= circleAverage (∑ c in s, log⁺ ‖f c ·‖ + log s.card) 0 r := by
      apply circleAverage_mono
      · apply (Meromorphic.fun_sum hf).meromorphicOn.circleIntegrable_posLog_norm
      · fun_prop
      · intro x hx
        rw [add_comm]
        apply posLog_norm_sum_le
    _ = ∑ c in s, circleAverage (log⁺ ‖f c ·‖) 0 r + log s.card := by
      nth_rw 2 [← circleAverage_const (log s.card) 0 r]
      rw [← circleAverage_sum h₂f]; rw [← circleAverage_add (CircleIntegrable.sum s h₂f)
        (circleIntegrable_const (log s.card) 0 r)]
      congr 1
      ext x
      simp

/--
theorem `proximity_add_top_le` / 定理 `proximity_add_top_le`

English:
theorem proximity_add_top_le
  statement: [NormedSpace Complex E] {f₁ f₂ : Complex -> E} (h₁f₁ : Meromorphic f₁)
  proof: by
  simpa using proximity_sum_top_le Finset.univ ![f₁, f₂]
    (fun i => by fin_cases i <;> aesop)

中文:
定理 proximity_add_top_le
  结论: [赋范空间 复形 E] {f₁ f₂ : 复形 -> E} (h₁f₁ : 亚纯 f₁)
  证明: by
  simpa using proximity_sum_top_le Finset.univ ![f₁, f₂]
    (fun i => by fin_cases i <;> aesop)

Depends on / 依赖: Finset, Finset.univ, fin_cases, proximity_sum_top_le
-/
theorem proximity_add_top_le [NormedSpace Complex E] {f₁ f₂ : Complex -> E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    proximity (f₁ + f₂) ⊤ <= (proximity f₁ ⊤) + (proximity f₂ ⊤) + (fun _ => log 2) := by
  simpa using proximity_sum_top_le Finset.univ ![f₁, f₂]
    (fun i => by fin_cases i <;> aesop)

/--
theorem `proximity_mul_top_le` / 定理 `proximity_mul_top_le`

English:
theorem proximity_mul_top_le
  given: {f₁ f₂ : Complex -> Complex} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂)
  proof: by
  calc proximity (f₁ * f₂) ⊤
    _ = circleAverage (fun x => log⁺ (‖f₁ x‖ * ‖f₂ x‖)) 0 := by
      simp [proximity]
    _ <= circleAverage (fun x => log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖) 0 := by
      intro r
      apply circleAverage_mono
      · simp_rw [← norm_mul]
        apply MeromorphicOn.circleInteg

中文:
定理 proximity_mul_top_le
  条件: {f₁ f₂ : 复形 -> 复形} (h₁f₁ : 亚纯 f₁) (h₁f₂ : 亚纯 f₂)
  证明: by
  calc proximity (f₁ * f₂) ⊤
    _ = circleAverage (fun x => log⁺ (‖f₁ x‖ * ‖f₂ x‖)) 0 := by
      simp [proximity]
    _ <= circleAverage (fun x => log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖) 0 := by
      intro r
      apply circleAverage_mono
      · simp_rw [← norm_mul]
        apply MeromorphicOn.circleInteg

Depends on / 依赖: Meromorphic, Meromorphic.meromorphicOn, MeromorphicOn, MeromorphicOn.circleIntegrable_posLog_norm, circleA, circleAverage, circleAverage_mono, circleIntegrable_posLog_norm, fun_prop, meromorphicOn, norm_mul, posLog_mul, proximity, simp_rw
-/
theorem proximity_mul_top_le {f₁ f₂ : Complex -> Complex} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    proximity (f₁ * f₂) ⊤ <= proximity f₁ ⊤ + proximity f₂ ⊤ := by
  calc proximity (f₁ * f₂) ⊤
    _ = circleAverage (fun x => log⁺ (‖f₁ x‖ * ‖f₂ x‖)) 0 := by
      simp [proximity]
    _ <= circleAverage (fun x => log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖) 0 := by
      intro r
      apply circleAverage_mono
      · simp_rw [← norm_mul]
        apply MeromorphicOn.circleIntegrable_posLog_norm
        apply Meromorphic.meromorphicOn
        fun_prop
      · apply (MeromorphicOn.circleIntegrable_posLog_norm (fun x a => h₁f₁ x)).add
          (MeromorphicOn.circleIntegrable_posLog_norm (fun x a => h₁f₂ x))
      · exact fun _ _ => posLog_mul
    _ = circleAverage (log⁺ ‖f₁ ·‖) 0 + circleAverage (log⁺ ‖f₂ ·‖) 0 := by
      ext r
      apply circleAverage_add
      · exact MeromorphicOn.circleIntegrable_posLog_norm (fun x a => h₁f₁ x)
      · exact MeromorphicOn.circleIntegrable_posLog_norm (fun x a => h₁f₂ x)
    _ = proximity f₁ ⊤ + proximity f₂ ⊤ := by simp [proximity]

/--
theorem `proximity_mul_zero_le` / 定理 `proximity_mul_zero_le`

English:
theorem proximity_mul_zero_le
  given: {f₁ f₂ : Complex -> Complex} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂)
  proof: by
  calc proximity (f₁ * f₂) 0
    _ <= (proximity f₁⁻¹ ⊤) + (proximity f₂⁻¹ ⊤) := by
      rw [← proximity_inv]; rw [mul_inv]
      apply proximity_mul_top_le h₁f₁.inv h₁f₂.inv
    _ = (proximity f₁ 0) + (proximity f₂ 0) := by
      rw [proximity_inv]; rw [proximity_inv]

中文:
定理 proximity_mul_zero_le
  条件: {f₁ f₂ : 复形 -> 复形} (h₁f₁ : 亚纯 f₁) (h₁f₂ : 亚纯 f₂)
  证明: by
  calc proximity (f₁ * f₂) 0
    _ <= (proximity f₁⁻¹ ⊤) + (proximity f₂⁻¹ ⊤) := by
      rw [← proximity_inv]; rw [mul_inv]
      apply proximity_mul_top_le h₁f₁.inv h₁f₂.inv
    _ = (proximity f₁ 0) + (proximity f₂ 0) := by
      rw [proximity_inv]; rw [proximity_inv]

Depends on / 依赖: mul_inv, proximity, proximity_inv, proximity_mul_top_le
-/
theorem proximity_mul_zero_le {f₁ f₂ : Complex -> Complex} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    proximity (f₁ * f₂) 0 <= (proximity f₁ 0) + (proximity f₂ 0) := by
  calc proximity (f₁ * f₂) 0
    _ <= (proximity f₁⁻¹ ⊤) + (proximity f₂⁻¹ ⊤) := by
      rw [← proximity_inv]; rw [mul_inv]
      apply proximity_mul_top_le h₁f₁.inv h₁f₂.inv
    _ = (proximity f₁ 0) + (proximity f₂ 0) := by
      rw [proximity_inv]; rw [proximity_inv]

/--
theorem `proximity_pow_top` / 定理 `proximity_pow_top`

English:
theorem proximity_pow_top
  given: {f : Complex -> Complex} {n : Nat}
  proof: by
  ext x
  simp [proximity, ← smul_eq_mul, circleAverage_fun_smul]

中文:
定理 proximity_pow_top
  条件: {f : 复形 -> 复形} {n : 自然数}
  证明: by
  ext x
  simp [proximity, ← smul_eq_mul, circleAverage_fun_smul]
-/
@[simp] theorem proximity_pow_top {f : Complex -> Complex} {n : Nat} :
    proximity (f ^ n) ⊤ = n • (proximity f ⊤) := by
  ext x
  simp [proximity, ← smul_eq_mul, circleAverage_fun_smul]

/--
theorem `proximity_pow_zero` / 定理 `proximity_pow_zero`

English:
theorem proximity_pow_zero
  given: {f : Complex -> Complex} {n : Nat}
  proof: by
  rw [← proximity_inv]; rw [← proximity_inv]; rw [← inv_pow]; rw [proximity_pow_top]

中文:
定理 proximity_pow_zero
  条件: {f : 复形 -> 复形} {n : 自然数}
  证明: by
  rw [← proximity_inv]; rw [← proximity_inv]; rw [← inv_pow]; rw [proximity_pow_top]
-/
@[simp] theorem proximity_pow_zero {f : Complex -> Complex} {n : Nat} :
    proximity (f ^ n) 0 = n • (proximity f 0) := by
  rw [← proximity_inv]; rw [← proximity_inv]; rw [← inv_pow]; rw [proximity_pow_top]

end ValueDistribution
