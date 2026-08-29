/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrals with exponential decay at ∞

As easy special cases of general theorems in the library, we prove the following test
for integrability:

* `integrable_of_isBigO_exp_neg`: If `f` is continuous on `[a,∞)`, for some `a ∈ ℝ`, and there
  exists `b > 0` such that `f(x) = O(exp(-b x))` as `x → ∞`, then `f` is integrable on `(a, ∞)`.
-/

public section


noncomputable section

open Real intervalIntegral MeasureTheory Set Filter

open scoped Topology

/--
theorem `exp_neg_integrableOn_Ioi` / 定理 `exp_neg_integrableOn_Ioi`

English:
theorem exp_neg_integrableOn_Ioi
  given: (a : Real) {b : Real} (h : 0 < b)
  proof: by
  have : Tendsto (fun x => -exp (-b * x) / b) atTop (𝓝 (-0 / b)) := by
    refine Tendsto.div_const (Tendsto.neg ?_) _
    exact tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 h))
  refine integrableOn_Ioi_deriv_of_nonneg' (fun x _ => ?_) (fun x _ => (exp_pos _).le) 

中文:
定理 exp_neg_integrableOn_Ioi
  条件: (a : 实数) {b : 实数} (h : 0 < b)
  证明: by
  have : Tendsto (fun x => -exp (-b * x) / b) atTop (𝓝 (-0 / b)) := by
    refine Tendsto.div_const (Tendsto.neg ?_) _
    exact tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 h))
  refine integrableOn_Ioi_deriv_of_nonneg' (fun x _ => ?_) (fun x _ => (exp_pos _).le) 

Depends on / 依赖: Tendsto, Tendsto.div_const, Tendsto.neg, const_mul, const_mul_atTop_of_neg, div_const, exp_pos, h.ne, hasDerivAt_id, integrableOn_Ioi_deriv_of_nonneg, neg.exp.neg.div_const, neg_neg_iff_pos, tendsto_exp_atBot, tendsto_exp_atBot.comp, tendsto_id, tendsto_id.const_mul_atTop_of_neg
-/
theorem exp_neg_integrableOn_Ioi (a : Real) {b : Real} (h : 0 < b) :
    IntegrableOn (fun x : Real => exp (-b * x)) (Ioi a) := by
  have : Tendsto (fun x => -exp (-b * x) / b) atTop (𝓝 (-0 / b)) := by
    refine Tendsto.div_const (Tendsto.neg ?_) _
    exact tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 h))
  refine integrableOn_Ioi_deriv_of_nonneg' (fun x _ => ?_) (fun x _ => (exp_pos _).le) this
  simpa [h.ne'] using ((hasDerivAt_id x).const_mul b).neg.exp.neg.div_const b

/--
theorem `integrable_of_isBigO_exp_neg` / 定理 `integrable_of_isBigO_exp_neg`

English:
theorem integrable_of_isBigO_exp_neg
  statement: {f : Real -> Real} {a b : Real} (h0 : 0 < b)
  proof: .mp integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)
    (hf.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    ho ⟨Ioi b, Ioi_mem_atTop b, exp_neg_integrableOn_Ioi b h0⟩

中文:
定理 integrable_of_isBigO_exp_neg
  结论: {f : 实数 -> 实数} {a b : 实数} (h0 : 0 < b)
  证明: .mp integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)
    (hf.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    ho ⟨Ioi b, Ioi_mem_atTop b, exp_neg_integrableOn_Ioi b h0⟩

Depends on / 依赖: Ioi_mem_atTop, exp_neg_integrableOn_Ioi, finiteness, hf.locallyIntegrableOn, integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_of_isBigO_atTop, locallyIntegrableOn, measurableSet_Ici
-/
theorem integrable_of_isBigO_exp_neg {f : Real -> Real} {a b : Real} (h0 : 0 < b)
    (hf : ContinuousOn f (Ici a)) (ho : f =O[atTop] fun x => exp (-b * x)) :
    IntegrableOn f (Ioi a) :=
.mp integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)
    (hf.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    ho ⟨Ioi b, Ioi_mem_atTop b, exp_neg_integrableOn_Ioi b h0⟩
