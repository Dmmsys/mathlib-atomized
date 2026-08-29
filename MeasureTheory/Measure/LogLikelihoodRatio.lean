/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Log-likelihood Ratio

The likelihood ratio between two measures `μ` and `ν` is their Radon-Nikodym derivative
`μ.rnDeriv ν`. The logarithm of that function is often used instead: this is the log-likelihood
ratio.

This file contains a definition of the log-likelihood ratio (llr) and its properties.

## Main definitions

* `llr μ ν`: Log-Likelihood Ratio between `μ` and `ν`, defined as the function
  `x ↦ log (μ.rnDeriv ν x).toReal`.

-/

@[expose] public section

open Real

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : α -> Real}

/--
Definition of `llr` / `llr` 的定义

English:
definition llr
  signature: (μ ν : Measure α) (x : α)
  body: log (μ.rnDeriv ν x).toReal

中文:
定义 llr
  签名: (μ ν : 测度 α) (x : α)
  定义体: log (μ.rnDeriv ν x).toReal

Depends on / 依赖: rnDeriv, toReal
-/
noncomputable def llr (μ ν : Measure α) (x : α) : Real := log (μ.rnDeriv ν x).toReal

/--
lemma `llr_def` / 引理 `llr_def`

English:
lemma llr_def
  given: (μ ν : Measure α)
  statement: llr μ ν = fun x => log (μ.rnDeriv ν x).toReal
  proof: rfl

中文:
引理 llr_def
  条件: (μ ν : 测度 α)
  结论: llr μ ν = fun x => log (μ.rnDeriv ν x).to实数
  证明: rfl
-/
lemma llr_def (μ ν : Measure α) : llr μ ν = fun x => log (μ.rnDeriv ν x).toReal := rfl

/--
lemma `llr_self` / 引理 `llr_self`

English:
lemma llr_self
  given: (μ : Measure α) [SigmaFinite μ]
  statement: llr μ μ =ᵐ[μ] 0
  proof: by
  filter_upwards [μ.rnDeriv_self] with a ha using by simp [llr, ha]

中文:
引理 llr_self
  条件: (μ : 测度 α) [σ有限 μ]
  结论: llr μ μ =ᵐ[μ] 0
  证明: by
  filter_upwards [μ.rnDeriv_self] with a ha using by simp [llr, ha]

Depends on / 依赖: filter_upwards, rnDeriv_self
-/
lemma llr_self (μ : Measure α) [SigmaFinite μ] : llr μ μ =ᵐ[μ] 0 := by
  filter_upwards [μ.rnDeriv_self] with a ha using by simp [llr, ha]

/--
lemma `exp_llr` / 引理 `exp_llr`

English:
lemma exp_llr
  given: (μ ν : Measure α) [SigmaFinite μ]
  proof: by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [llr, h_zero, ENNReal.toReal_zero, log_zero, exp_zero, ite_true]
  · rw [llr, exp_log, if_neg h_zero]
    exact ENNReal.toReal_pos h_zero hx.ne

中文:
引理 exp_llr
  条件: (μ ν : 测度 α) [σ有限 μ]
  证明: by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [llr, h_zero, ENNReal.toReal_zero, log_zero, exp_zero, ite_true]
  · rw [llr, exp_log, if_neg h_zero]
    exact ENNReal.toReal_pos h_zero hx.ne

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, ENNReal.toReal_zero, Measure, Measure.rnDeriv_lt_top, exp_log, exp_zero, filter_upwards, h_zero, hx.ne, if_neg, ite_true, log_zero, rnDeriv, rnDeriv_lt_top, toReal_pos, toReal_zero
-/
lemma exp_llr (μ ν : Measure α) [SigmaFinite μ] :
    (fun x => exp (llr μ ν x))
      =ᵐ[ν] fun x => if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [llr, h_zero, ENNReal.toReal_zero, log_zero, exp_zero, ite_true]
  · rw [llr, exp_log, if_neg h_zero]
    exact ENNReal.toReal_pos h_zero hx.ne

/--
lemma `exp_llr_of_ac` / 引理 `exp_llr_of_ac`

English:
lemma exp_llr_of_ac
  statement: (μ ν : Measure α) [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν]
  proof: by
  filter_upwards [hμν.ae_le (exp_llr μ ν), Measure.rnDeriv_pos hμν] with x hx_eq hx_pos
  rw [hx_eq]; rw [if_neg hx_pos.ne']

中文:
引理 exp_llr_of_ac
  结论: (μ ν : 测度 α) [σ有限 μ] [测度.有Lebesgue分解 μ ν]
  证明: by
  filter_upwards [hμν.ae_le (exp_llr μ ν), Measure.rnDeriv_pos hμν] with x hx_eq hx_pos
  rw [hx_eq]; rw [if_neg hx_pos.ne']

Depends on / 依赖: Measure, Measure.rnDeriv_pos, ae_le, exp_llr, filter_upwards, hx_eq, hx_pos, hx_pos.ne, if_neg, rnDeriv_pos
-/
lemma exp_llr_of_ac (μ ν : Measure α) [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) :
    (fun x => exp (llr μ ν x)) =ᵐ[μ] fun x => (μ.rnDeriv ν x).toReal := by
  filter_upwards [hμν.ae_le (exp_llr μ ν), Measure.rnDeriv_pos hμν] with x hx_eq hx_pos
  rw [hx_eq]; rw [if_neg hx_pos.ne']

/--
lemma `exp_llr_of_ac'` / 引理 `exp_llr_of_ac'`

English:
lemma exp_llr_of_ac'
  given: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ)
  proof: by
  filter_upwards [exp_llr μ ν, Measure.rnDeriv_pos' hμν] with x hx hx_pos
  rwa [if_neg hx_pos.ne'] at hx

中文:
引理 exp_llr_of_ac'
  条件: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν] (hμν : ν ≪ μ)
  证明: by
  filter_upwards [exp_llr μ ν, Measure.rnDeriv_pos' hμν] with x hx hx_pos
  rwa [if_neg hx_pos.ne'] at hx

Depends on / 依赖: Measure, Measure.rnDeriv_pos, exp_llr, filter_upwards, hx_pos, hx_pos.ne, if_neg, rnDeriv_pos
-/
lemma exp_llr_of_ac' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x => exp (llr μ ν x)) =ᵐ[ν] fun x => (μ.rnDeriv ν x).toReal := by
  filter_upwards [exp_llr μ ν, Measure.rnDeriv_pos' hμν] with x hx hx_pos
  rwa [if_neg hx_pos.ne'] at hx

/--
lemma `neg_llr` / 引理 `neg_llr`

English:
lemma neg_llr
  given: [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
  proof: by
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [Pi.neg_apply]; rw [llr]; rw [llr]; rw [← log_inv]; rw [← ENNReal.toReal_inv]
  congr

中文:
引理 neg_llr
  条件: [σ有限 μ] [σ有限 ν] (hμν : μ ≪ ν)
  证明: by
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [Pi.neg_apply]; rw [llr]; rw [llr]; rw [← log_inv]; rw [← ENNReal.toReal_inv]
  congr

Depends on / 依赖: ENNReal, ENNReal.toReal_inv, Measure, Measure.inv_rnDeriv, Pi.neg_apply, filter_upwards, inv_rnDeriv, log_inv, neg_apply, toReal_inv
-/
lemma neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    -llr μ ν =ᵐ[μ] llr ν μ := by
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [Pi.neg_apply]; rw [llr]; rw [llr]; rw [← log_inv]; rw [← ENNReal.toReal_inv]
  congr

/--
lemma `exp_neg_llr` / 引理 `exp_neg_llr`

English:
lemma exp_neg_llr
  given: [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
  proof: by
  filter_upwards [neg_llr hμν, exp_llr_of_ac' ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply] at hx
  rw [hx]; rw [hx_exp_log]

中文:
引理 exp_neg_llr
  条件: [σ有限 μ] [σ有限 ν] (hμν : μ ≪ ν)
  证明: by
  filter_upwards [neg_llr hμν, exp_llr_of_ac' ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply] at hx
  rw [hx]; rw [hx_exp_log]

Depends on / 依赖: Pi.neg_apply, exp_llr_of_ac, filter_upwards, hx_exp_log, neg_apply, neg_llr
-/
lemma exp_neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x => exp (-llr μ ν x)) =ᵐ[μ] fun x => (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr_of_ac' ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply] at hx
  rw [hx]; rw [hx_exp_log]

/--
lemma `exp_neg_llr'` / 引理 `exp_neg_llr'`

English:
lemma exp_neg_llr'
  given: [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ)
  proof: by
  filter_upwards [neg_llr hμν, exp_llr_of_ac ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply]; rw [neg_eq_iff_eq_neg] at hx
  rw [← hx]; rw [hx_exp_log]

@[fun_prop]

中文:
引理 exp_neg_llr'
  条件: [σ有限 μ] [σ有限 ν] (hμν : ν ≪ μ)
  证明: by
  filter_upwards [neg_llr hμν, exp_llr_of_ac ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply]; rw [neg_eq_iff_eq_neg] at hx
  rw [← hx]; rw [hx_exp_log]

@[fun_prop]

Depends on / 依赖: Pi.neg_apply, exp_llr_of_ac, filter_upwards, hx_exp_log, neg_apply, neg_eq_iff_eq_neg, neg_llr
-/
lemma exp_neg_llr' [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x => exp (-llr μ ν x)) =ᵐ[ν] fun x => (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr_of_ac ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply]; rw [neg_eq_iff_eq_neg] at hx
  rw [← hx]; rw [hx_exp_log]

@[fun_prop]
/--
lemma `measurable_llr` / 引理 `measurable_llr`

English:
lemma measurable_llr
  given: (μ ν : Measure α)
  statement: Measurable (llr μ ν)
  proof: (Measure.measurable_rnDeriv μ ν).ennreal_toReal.log

@[fun_prop]

中文:
引理 measurable_llr
  条件: (μ ν : 测度 α)
  结论: 可测 (llr μ ν)
  证明: (Measure.measurable_rnDeriv μ ν).ennreal_toReal.log

@[fun_prop]

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, ennreal_toReal, ennreal_toReal.log, measurable_rnDeriv
-/
lemma measurable_llr (μ ν : Measure α) : Measurable (llr μ ν) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal.log

@[fun_prop]
/--
lemma `stronglyMeasurable_llr` / 引理 `stronglyMeasurable_llr`

English:
lemma stronglyMeasurable_llr
  given: (μ ν : Measure α)
  statement: StronglyMeasurable (llr μ ν)
  proof: (measurable_llr μ ν).stronglyMeasurable

中文:
引理 stronglyMeasurable_llr
  条件: (μ ν : 测度 α)
  结论: StronglyMeasurable (llr μ ν)
  证明: (measurable_llr μ ν).stronglyMeasurable

Depends on / 依赖: measurable_llr, stronglyMeasurable
-/
lemma stronglyMeasurable_llr (μ ν : Measure α) : StronglyMeasurable (llr μ ν) :=
  (measurable_llr μ ν).stronglyMeasurable

/--
lemma `llr_smul_left` / 引理 `llr_smul_left`

English:
lemma llr_smul_left
  statement: [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
  proof: by
  simp only [llr, llr_def]
  have h := Measure.rnDeriv_smul_left_of_ne_top μ ν hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw

中文:
引理 llr_smul_left
  结论: [是有限测度 μ] [测度.有Lebesgue分解 μ ν]
  证明: by
  simp only [llr, llr_def]
  have h := Measure.rnDeriv_smul_left_of_ne_top μ ν hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_ne_zero, Measure, Measure.rnDeriv_lt_top, Measure.rnDeriv_pos, Measure.rnDeriv_smul_left_of_ne_top, Pi.smul_apply, ae_le, filter_upwards, hc_ne_top, hx_eq, hx_ne_top, hx_ne_top.ne, hx_pos, hx_pos.ne, llr_def, log_mul, rnDeriv_lt_top, rnDeriv_pos
-/
lemma llr_smul_left [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne_top : c != ∞) :
    llr (c • μ) ν =ᵐ[μ] fun x => llr μ ν x + log c.toReal := by
  simp only [llr, llr_def]
  have h := Measure.rnDeriv_smul_left_of_ne_top μ ν hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  ring

/--
lemma `llr_smul_nnreal_left` / 引理 `llr_smul_nnreal_left`

English:
lemma llr_smul_nnreal_left
  statement: [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
  proof: by
  rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_left hμν (c : Real>=0∞) (by simpa) (by simp)] with x hx
  rw [hx]
  simp

中文:
引理 llr_smul_nnreal_left
  结论: [是有限测度 μ] [测度.有Lebesgue分解 μ ν]
  证明: by
  rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_left hμν (c : Real>=0∞) (by simpa) (by simp)] with x hx
  rw [hx]
  simp

Depends on / 依赖: Measure, Measure.coe_nnreal_smul, coe_nnreal_smul, filter_upwards, llr_smul_left
-/
lemma llr_smul_nnreal_left [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : Real>=0) (hc : c != 0) :
    llr (c • μ) ν =ᵐ[μ] fun x => llr μ ν x + log c := by
  rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_left hμν (c : Real>=0∞) (by simpa) (by simp)] with x hx
  rw [hx]
  simp

/--
lemma `llr_smul_right` / 引理 `llr_smul_right`

English:
lemma llr_smul_right
  statement: [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
  proof: by
  simp only [llr, llr_def]
  have h := Measure.rnDeriv_smul_right_of_ne_top μ ν hc hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]


中文:
引理 llr_smul_right
  结论: [是有限测度 μ] [测度.有Lebesgue分解 μ ν]
  证明: by
  simp only [llr, llr_def]
  have h := Measure.rnDeriv_smul_right_of_ne_top μ ν hc hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]


Depends on / 依赖: ENNReal, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ne_zero, Measure, Measure.rnDeriv_lt_top, Measure.rnDeriv_pos, Measure.rnDeriv_smul_right_of_ne_top, Pi.smul_apply, ae_le, filter_upwards, hc_ne_top, hx_eq, hx_ne_top, hx_ne_top.ne, hx_pos, hx_pos.ne, llr_def, log_inv, log_mul
-/
lemma llr_smul_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne_top : c != ∞) :
    llr μ (c • ν) =ᵐ[μ] fun x => llr μ ν x - log c.toReal := by
  simp only [llr, llr_def]
  have h := Measure.rnDeriv_smul_right_of_ne_top μ ν hc hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  rw [ENNReal.toReal_inv]; rw [log_inv]
  ring

/--
lemma `llr_smul_nnreal_right` / 引理 `llr_smul_nnreal_right`

English:
lemma llr_smul_nnreal_right
  statement: [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
  proof: by
  rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_right hμν (c : Real>=0∞) (by simpa) (by simp)] with x hx
  rw [hx]
  simp

中文:
引理 llr_smul_nnreal_right
  结论: [是有限测度 μ] [测度.有Lebesgue分解 μ ν]
  证明: by
  rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_right hμν (c : Real>=0∞) (by simpa) (by simp)] with x hx
  rw [hx]
  simp

Depends on / 依赖: Measure, Measure.coe_nnreal_smul, coe_nnreal_smul, filter_upwards, llr_smul_right
-/
lemma llr_smul_nnreal_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : Real>=0) (hc : c != 0) :
    llr μ (c • ν) =ᵐ[μ] fun x => llr μ ν x - log c := by
  rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_right hμν (c : Real>=0∞) (by simpa) (by simp)] with x hx
  rw [hx]
  simp

/--
lemma `llr_smul_inv_left_eq_smul_right` / 引理 `llr_smul_inv_left_eq_smul_right`

English:
lemma llr_smul_inv_left_eq_smul_right
  statement: [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
  proof: by
  have hc' : c⁻¹ != 0 := by simp [hc_ne_top]
  have hc_ne_top' : c⁻¹ != ∞ := by simp [hc]
  filter_upwards [llr_smul_left hμν c⁻¹ hc' hc_ne_top', llr_smul_right hμν c hc hc_ne_top] with
    x hx_left hx_right
  rw [hx_left]; rw [hx_right]
  simp [sub_eq_add_neg]

中文:
引理 llr_smul_inv_left_eq_smul_right
  结论: [是有限测度 μ] [测度.有Lebesgue分解 μ ν]
  证明: by
  have hc' : c⁻¹ != 0 := by simp [hc_ne_top]
  have hc_ne_top' : c⁻¹ != ∞ := by simp [hc]
  filter_upwards [llr_smul_left hμν c⁻¹ hc' hc_ne_top', llr_smul_right hμν c hc hc_ne_top] with
    x hx_left hx_right
  rw [hx_left]; rw [hx_right]
  simp [sub_eq_add_neg]

Depends on / 依赖: filter_upwards, hc_ne_top, hx_left, hx_right, llr_smul_left, llr_smul_right, sub_eq_add_neg
-/
lemma llr_smul_inv_left_eq_smul_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne_top : c != ∞) :
    llr (c⁻¹ • μ) ν =ᵐ[μ] llr μ (c • ν) := by
  have hc' : c⁻¹ != 0 := by simp [hc_ne_top]
  have hc_ne_top' : c⁻¹ != ∞ := by simp [hc]
  filter_upwards [llr_smul_left hμν c⁻¹ hc' hc_ne_top', llr_smul_right hμν c hc hc_ne_top] with
    x hx_left hx_right
  rw [hx_left]; rw [hx_right]
  simp [sub_eq_add_neg]

/--
lemma `llr_smul_same` / 引理 `llr_smul_same`

English:
lemma llr_smul_same
  statement: [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
  proof: by
  simp only [llr_def]
  lift c to Real>=0 using hc_ne_top
  norm_cast at hc
  filter_upwards [hμν.ae_le (Measure.rnDeriv_smul_same μ ν hc)] with x hx using by simp [hx]

中文:
引理 llr_smul_same
  结论: [是有限测度 μ] [测度.有Lebesgue分解 μ ν]
  证明: by
  simp only [llr_def]
  lift c to Real>=0 using hc_ne_top
  norm_cast at hc
  filter_upwards [hμν.ae_le (Measure.rnDeriv_smul_same μ ν hc)] with x hx using by simp [hx]

Depends on / 依赖: Measure, Measure.rnDeriv_smul_same, ae_le, filter_upwards, hc_ne_top, llr_def, rnDeriv_smul_same
-/
lemma llr_smul_same [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne_top : c != ∞) :
    llr (c • μ) (c • ν) =ᵐ[μ] llr μ ν := by
  simp only [llr_def]
  lift c to Real>=0 using hc_ne_top
  norm_cast at hc
  filter_upwards [hμν.ae_le (Measure.rnDeriv_smul_same μ ν hc)] with x hx using by simp [hx]

/--
lemma `llr_smul_nnreal_same` / 引理 `llr_smul_nnreal_same`

English:
lemma llr_smul_nnreal_same
  statement: [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
  proof: by
  simp_rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_same hμν (c : Real>=0∞) (by simpa) (by simp)] with x hx
  rw [hx]

中文:
引理 llr_smul_nnreal_same
  结论: [是有限测度 μ] [测度.有Lebesgue分解 μ ν]
  证明: by
  simp_rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_same hμν (c : Real>=0∞) (by simpa) (by simp)] with x hx
  rw [hx]

Depends on / 依赖: Measure, Measure.coe_nnreal_smul, coe_nnreal_smul, filter_upwards, llr_smul_same, simp_rw
-/
lemma llr_smul_nnreal_same [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : Real>=0) (hc : c != 0) :
    llr (c • μ) (c • ν) =ᵐ[μ] llr μ ν := by
  simp_rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_same hμν (c : Real>=0∞) (by simpa) (by simp)] with x hx
  rw [hx]

/--
lemma `integrable_rnDeriv_mul_log_iff` / 引理 `integrable_rnDeriv_mul_log_iff`

English:
lemma integrable_rnDeriv_mul_log_iff
  given: [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν)
  proof: integrable_rnDeriv_smul_iff hμν

中文:
引理 integrable_rnDeriv_mul_log_iff
  条件: [σ有限 μ] [μ.有Lebesgue分解 ν] (hμν : μ ≪ ν)
  证明: integrable_rnDeriv_smul_iff hμν

Depends on / 依赖: integrable_rnDeriv_smul_iff
-/
lemma integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) :
    Integrable (fun a => (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal) ν
      ↔ Integrable (llr μ ν) μ :=
  integrable_rnDeriv_smul_iff hμν

/--
lemma `integral_rnDeriv_mul_log` / 引理 `integral_rnDeriv_mul_log`

English:
lemma integral_rnDeriv_mul_log
  given: [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν)
  proof: by
  simp_rw [← smul_eq_mul, integral_rnDeriv_smul hμν, llr]

中文:
引理 integral_rnDeriv_mul_log
  条件: [σ有限 μ] [μ.有Lebesgue分解 ν] (hμν : μ ≪ ν)
  证明: by
  simp_rw [← smul_eq_mul, integral_rnDeriv_smul hμν, llr]

Depends on / 依赖: integral_rnDeriv_smul, simp_rw, smul_eq_mul
-/
lemma integral_rnDeriv_mul_log [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) :
    ∫ a, (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal ∂ν = ∫ a, llr μ ν a ∂μ := by
  simp_rw [← smul_eq_mul, integral_rnDeriv_smul hμν, llr]

section llr_tilted

/--
lemma `llr_tilted_left` / 引理 `llr_tilted_left`

English:
lemma llr_tilted_left
  statement: [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
  proof: by
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_left μ hfν), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top


中文:
引理 llr_tilted_left
  结论: [σ有限 μ] [σ有限 ν] (hμν : μ ≪ ν)
  证明: by
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_left μ hfν), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top


Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Filter.eventually_bot, Measure, Measure.rnDeriv_lt_top, Measure.rnDeriv_pos, ae_le, ae_zero, div_eq_mul_inv, eq_zero_or_neZero, eventually_bot, exp_pos, filter_upwards, hx_lt_top, hx_pos, integral_exp_pos, inv_eq_zero, log_exp, log_inv
-/
lemma llr_tilted_left [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (hf : Integrable (fun x => exp (f x)) μ) (hfν : AEMeasurable f ν) :
    (llr (μ.tilted f) ν) =ᵐ[μ] fun x => f x - log (∫ z, exp (f z) ∂μ) + llr μ ν x := by
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_left μ hfν), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
    rw [llr]; rw [hx]; rw [log_mul]; rw [div_eq_mul_inv]; rw [log_mul (exp_pos _).ne']; rw [log_exp]; rw [log_inv]; rw [llr]; rw [← sub_eq_add_neg]
    · simp only [ne_eq, inv_eq_zero]
      exact (integral_exp_pos hf).ne'
    · simp only [ne_eq, div_eq_zero_iff]
      push Not
      exact ⟨(exp_pos _).ne', (integral_exp_pos hf).ne'⟩
    · simp [ENNReal.toReal_eq_zero_iff, hx_lt_top.ne, hx_pos.ne']

/--
lemma `integrable_llr_tilted_left` / 引理 `integrable_llr_tilted_left`

English:
lemma integrable_llr_tilted_left
  statement: [IsFiniteMeasure μ] [SigmaFinite ν]
  proof: by
  rw [integrable_congr (llr_tilted_left hμν hfμ hfν)]
  exact Integrable.add (hf.sub (integrable_const _)) h_int

中文:
引理 integrable_llr_tilted_left
  结论: [是有限测度 μ] [σ有限 ν]
  证明: by
  rw [integrable_congr (llr_tilted_left hμν hfμ hfν)]
  exact Integrable.add (hf.sub (integrable_const _)) h_int

Depends on / 依赖: Integrable, Integrable.add, h_int, hf.sub, integrable_congr, integrable_const, llr_tilted_left
-/
lemma integrable_llr_tilted_left [IsFiniteMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ)
    (hfμ : Integrable (fun x => exp (f x)) μ) (hfν : AEMeasurable f ν) :
    Integrable (llr (μ.tilted f) ν) μ := by
  rw [integrable_congr (llr_tilted_left hμν hfμ hfν)]
  exact Integrable.add (hf.sub (integrable_const _)) h_int

/--
lemma `integral_llr_tilted_left` / 引理 `integral_llr_tilted_left`

English:
lemma integral_llr_tilted_left
  statement: [IsProbabilityMeasure μ] [SigmaFinite ν]
  proof: by
  calc ∫ x, llr (μ.tilted f) ν x ∂μ
    = ∫ x, f x - log (∫ x, exp (f x) ∂μ) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_left hμν hfμ hfν)
  _ = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) + ∫ x, llr μ ν x ∂μ := by
        rw [integral_add ?_ h_int]
        swap; · exact hf.sub (integrable_

中文:
引理 integral_llr_tilted_left
  结论: [是概率测度 μ] [σ有限 ν]
  证明: by
  calc ∫ x, llr (μ.tilted f) ν x ∂μ
    = ∫ x, f x - log (∫ x, exp (f x) ∂μ) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_left hμν hfμ hfν)
  _ = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) + ∫ x, llr μ ν x ∂μ := by
        rw [integral_add ?_ h_int]
        swap; · exact hf.sub (integrable_

Depends on / 依赖: h_int, hf.sub, integrable_const, integral_add, integral_congr_ae, integral_const, integral_sub, llr_tilted_left, one_mul, probReal_univ, smul_eq_mul, tilted
-/
lemma integral_llr_tilted_left [IsProbabilityMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ)
    (hfμ : Integrable (fun x => exp (f x)) μ) (hfν : AEMeasurable f ν) :
    ∫ x, llr (μ.tilted f) ν x ∂μ = ∫ x, llr μ ν x ∂μ + ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) := by
  calc ∫ x, llr (μ.tilted f) ν x ∂μ
    = ∫ x, f x - log (∫ x, exp (f x) ∂μ) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_left hμν hfμ hfν)
  _ = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) + ∫ x, llr μ ν x ∂μ := by
        rw [integral_add ?_ h_int]
        swap; · exact hf.sub (integrable_const _)
        rw [integral_sub hf (integrable_const _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  _ = ∫ x, llr μ ν x ∂μ + ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) := by abel

/--
lemma `llr_tilted_right` / 引理 `llr_tilted_right`

English:
lemma llr_tilted_right
  statement: [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  cases eq_zero_or_neZero ν with
  | inl h =>
    have hμ : μ = 0 := by ext s _; exact hμν (by simp [h])
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_right μ ν hf), Measure.rnDeriv_pos hμν,
      hμν.ae_

中文:
引理 llr_tilted_right
  结论: [σ有限 μ] [σ有限 ν]
  证明: by
  cases eq_zero_or_neZero ν with
  | inl h =>
    have hμ : μ = 0 := by ext s _; exact hμν (by simp [h])
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_right μ ν hf), Measure.rnDeriv_pos hμν,
      hμν.ae_

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Filter.eventually_bot, Measure, Measure.rnDeriv_lt_top, Measure.rnDeriv_pos, ae_le, ae_zero, eq_zero_or_neZero, eventually_bot, exp_pos, filter_upwards, hx_lt_top, hx_pos, integral_exp_, integral_exp_pos, log_exp, log_mul, mul_pos
-/
lemma llr_tilted_right [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hf : Integrable (fun x => exp (f x)) ν) :
    (llr μ (ν.tilted f)) =ᵐ[μ] fun x => -f x + log (∫ z, exp (f z) ∂ν) + llr μ ν x := by
  cases eq_zero_or_neZero ν with
  | inl h =>
    have hμ : μ = 0 := by ext s _; exact hμν (by simp [h])
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_right μ ν hf), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
    rw [llr]; rw [hx]; rw [log_mul]; rw [log_mul (exp_pos _).ne']; rw [log_exp]; rw [llr]
    · exact (integral_exp_pos hf).ne'
    · refine (mul_pos (exp_pos _) (integral_exp_pos hf)).ne'
    · simp [ENNReal.toReal_eq_zero_iff, hx_lt_top.ne, hx_pos.ne']

/--
lemma `integrable_llr_tilted_right` / 引理 `integrable_llr_tilted_right`

English:
lemma integrable_llr_tilted_right
  statement: [IsFiniteMeasure μ] [SigmaFinite ν]
  proof: by
  rw [integrable_congr (llr_tilted_right hμν hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

中文:
引理 integrable_llr_tilted_right
  结论: [是有限测度 μ] [σ有限 ν]
  证明: by
  rw [integrable_congr (llr_tilted_right hμν hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

Depends on / 依赖: Integrable, Integrable.add, h_int, integrable_congr, integrable_const, llr_tilted_right, neg.add
-/
lemma integrable_llr_tilted_right [IsFiniteMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hfμ : Integrable f μ)
    (h_int : Integrable (llr μ ν) μ) (hfν : Integrable (fun x => exp (f x)) ν) :
    Integrable (llr μ (ν.tilted f)) μ := by
  rw [integrable_congr (llr_tilted_right hμν hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

/--
lemma `integral_llr_tilted_right` / 引理 `integral_llr_tilted_right`

English:
lemma integral_llr_tilted_right
  statement: [IsProbabilityMeasure μ] [SigmaFinite ν]
  proof: by
  calc ∫ x, llr μ (ν.tilted f) x ∂μ
    = ∫ x, -f x + log (∫ x, exp (f x) ∂ν) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_right hμν hfν)
  _ = -∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) + ∫ x, llr μ ν x ∂μ := by
        rw [← integral_neg]; rw [integral_add ?_ h_int]
        swap; · exact

中文:
引理 integral_llr_tilted_right
  结论: [是概率测度 μ] [σ有限 ν]
  证明: by
  calc ∫ x, llr μ (ν.tilted f) x ∂μ
    = ∫ x, -f x + log (∫ x, exp (f x) ∂ν) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_right hμν hfν)
  _ = -∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) + ∫ x, llr μ ν x ∂μ := by
        rw [← integral_neg]; rw [integral_add ?_ h_int]
        swap; · exact

Depends on / 依赖: h_int, integrable_const, integral_add, integral_congr_ae, integral_const, integral_neg, llr_tilted_right, neg.add, one_mul, probReal_univ, smul_eq_mul, tilted
-/
lemma integral_llr_tilted_right [IsProbabilityMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x => exp (f x)) ν)
    (h_int : Integrable (llr μ ν) μ) :
    ∫ x, llr μ (ν.tilted f) x ∂μ = ∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by
  calc ∫ x, llr μ (ν.tilted f) x ∂μ
    = ∫ x, -f x + log (∫ x, exp (f x) ∂ν) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_right hμν hfν)
  _ = -∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) + ∫ x, llr μ ν x ∂μ := by
        rw [← integral_neg]; rw [integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  _ = ∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by abel

end llr_tilted

end MeasureTheory
