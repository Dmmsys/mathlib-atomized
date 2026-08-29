/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Properties of the extended logarithm and exponential

We prove that `log` and `exp` define order isomorphisms between `ℝ≥0∞` and `EReal`.

## Main Definitions
- `ENNReal.logOrderIso`: The order isomorphism between `ℝ≥0∞` and `EReal` defined by `log`
  and `exp`.
- `EReal.expOrderIso`: The order isomorphism between `EReal` and `ℝ≥0∞` defined by `exp`
  and `log`.
- `ENNReal.logHomeomorph`: `log` as a homeomorphism.
- `EReal.expHomeomorph`: `exp` as a homeomorphism.

## Main Results
- `EReal.log_exp`, `ENNReal.exp_log`: `log` and `exp` are inverses of each other.
- `EReal.exp_nmul`, `EReal.exp_mul`: `exp` satisfies the identities `exp (n * x) = (exp x) ^ n`
  and `exp (x * y) = (exp x) ^ y`.
- `EReal` is a Polish space.

## Tags
ENNReal, EReal, logarithm, exponential
-/

@[expose] public section

open EReal ENNReal Topology
section LogExp

/--
lemma `EReal.log_exp` / 引理 `EReal.log_exp`

English:
lemma EReal.log_exp
  given: (x : EReal)
  statement: log (exp x) = x
  proof: by
  induction x
  · simp
  · rw [exp_coe, log_ofReal, if_neg (not_le.mpr (Real.exp_pos _)), Real.log_exp]
  · simp

中文:
引理 EReal.log_exp
  条件: (x : E实数)
  结论: log (exp x) = x
  证明: by
  induction x
  · simp
  · rw [exp_coe, log_ofReal, if_neg (not_le.mpr (Real.exp_pos _)), Real.log_exp]
  · simp
-/
@[simp] lemma EReal.log_exp (x : EReal) : log (exp x) = x := by
  induction x
  · simp
  · rw [exp_coe, log_ofReal, if_neg (not_le.mpr (Real.exp_pos _)), Real.log_exp]
  · simp

/--
lemma `ENNReal.exp_log` / 引理 `ENNReal.exp_log`

English:
lemma ENNReal.exp_log
  given: (x : Real>=0∞)
  statement: exp (log x) = x
  proof: by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top]; rw [log_ofReal_of_pos hx_pos]; rw [exp_coe]; rw [Real.exp_log hx_pos]

中文:
引理 ENNReal.exp_log
  条件: (x : 实数>=0∞)
  结论: exp (log x) = x
  证明: by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top]; rw [log_ofReal_of_pos hx_pos]; rw [exp_coe]; rw [Real.exp_log hx_pos]
-/
@[simp] lemma ENNReal.exp_log (x : Real>=0∞) : exp (log x) = x := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top]; rw [log_ofReal_of_pos hx_pos]; rw [exp_coe]; rw [Real.exp_log hx_pos]

end LogExp

section Exp
namespace EReal

/--
lemma `exp_nmul` / 引理 `exp_nmul`

English:
lemma exp_nmul
  given: (x : EReal) (n : Nat)
  statement: exp (n * x) = (exp x) ^ n
  proof: by
  simp_rw [← log_eq_iff, log_pow, log_exp]

中文:
引理 exp_nmul
  条件: (x : E实数) (n : 自然数)
  结论: exp (n * x) = (exp x) ^ n
  证明: by
  simp_rw [← log_eq_iff, log_pow, log_exp]

Depends on / 依赖: log_eq_iff, log_exp, log_pow, simp_rw
-/
lemma exp_nmul (x : EReal) (n : Nat) : exp (n * x) = (exp x) ^ n := by
  simp_rw [← log_eq_iff, log_pow, log_exp]

/--
lemma `exp_mul` / 引理 `exp_mul`

English:
lemma exp_mul
  given: (x : EReal) (y : Real)
  statement: exp (x * y) = (exp x) ^ y
  proof: by
  rw [← log_eq_iff]; rw [log_rpow]; rw [log_exp]; rw [log_exp]; rw [mul_comm]

中文:
引理 exp_mul
  条件: (x : E实数) (y : 实数)
  结论: exp (x * y) = (exp x) ^ y
  证明: by
  rw [← log_eq_iff]; rw [log_rpow]; rw [log_exp]; rw [log_exp]; rw [mul_comm]

Depends on / 依赖: log_eq_iff, log_exp, log_rpow, mul_comm
-/
lemma exp_mul (x : EReal) (y : Real) : exp (x * y) = (exp x) ^ y := by
  rw [← log_eq_iff]; rw [log_rpow]; rw [log_exp]; rw [log_exp]; rw [mul_comm]

end EReal
end Exp

namespace ENNReal

/--
lemma `rpow_eq_exp_mul_log` / 引理 `rpow_eq_exp_mul_log`

English:
lemma rpow_eq_exp_mul_log
  given: (x : Real>=0∞) (y : Real)
  statement: x ^ y = exp (y * log x)
  proof: by
  rw [← log_rpow]; rw [exp_log]

@[deprecated (since := "2026-07-15")] alias _root_.EReal.ENNReal.rpow_eq_exp_mul_log :=
  rpow_eq_exp_mul_log

中文:
引理 rpow_eq_exp_mul_log
  条件: (x : 实数>=0∞) (y : 实数)
  结论: x ^ y = exp (y * log x)
  证明: by
  rw [← log_rpow]; rw [exp_log]

@[deprecated (since := "2026-07-15")] alias _root_.EReal.ENNReal.rpow_eq_exp_mul_log :=
  rpow_eq_exp_mul_log

Depends on / 依赖: exp_log, log_rpow
-/
lemma rpow_eq_exp_mul_log (x : Real>=0∞) (y : Real) : x ^ y = exp (y * log x) := by
  rw [← log_rpow]; rw [exp_log]

@[deprecated (since := "2026-07-15")] alias _root_.EReal.ENNReal.rpow_eq_exp_mul_log :=
  rpow_eq_exp_mul_log

section OrderIso

set_option backward.isDefEq.respectTransparency false in
/-- `ENNReal.log` and its inverse `EReal.exp` are an order isomorphism between `ℝ≥0∞` and
`EReal`. -/
noncomputable
/--
Definition of `logOrderIso` / `logOrderIso` 的定义

English:
definition logOrderIso
  signature: : Real>=0∞ ≃o EReal where
  body: log
  invFun := exp
  left_inv x := exp_log x
  right_inv x := log_exp x
  map_rel_iff' := by simp only [Equiv.coe_fn_mk, log_le_log_iff, forall_const]

中文:
定义 logOrderIso
  签名: : 实数>=0∞ ≃o E实数 where
  定义体: log
  invFun := exp
  left_inv x := exp_log x
  right_inv x := log_exp x
  map_rel_iff' := by simp only [Equiv.coe_fn_mk, log_le_log_iff, forall_const]
-/
def logOrderIso : Real>=0∞ ≃o EReal where
  toFun := log
  invFun := exp
  left_inv x := exp_log x
  right_inv x := log_exp x
  map_rel_iff' := by simp only [Equiv.coe_fn_mk, log_le_log_iff, forall_const]

/--
lemma `logOrderIso_apply` / 引理 `logOrderIso_apply`

English:
lemma logOrderIso_apply
  given: (x : Real>=0∞)
  statement: logOrderIso x = log x
  proof: rfl

中文:
引理 logOrderIso_apply
  条件: (x : 实数>=0∞)
  结论: logOrderIso x = log x
  证明: rfl
-/
@[simp] lemma logOrderIso_apply (x : Real>=0∞) : logOrderIso x = log x := rfl

/-- `EReal.exp` and its inverse `ENNReal.log` are an order isomorphism between `EReal` and
`ℝ≥0∞`. -/
noncomputable
/--
Definition of `_root_.EReal.expOrderIso` / `_root_.EReal.expOrderIso` 的定义

English:
definition _root_.EReal.expOrderIso
  body: logOrderIso.symm

中文:
定义 _root_.EReal.expOrderIso
  定义体: logOrderIso.symm

Depends on / 依赖: logOrderIso, logOrderIso.symm
-/
def _root_.EReal.expOrderIso := logOrderIso.symm

/--
lemma `_root_.EReal.expOrderIso_apply` / 引理 `_root_.EReal.expOrderIso_apply`

English:
lemma _root_.EReal.expOrderIso_apply
  given: (x : EReal)
  statement: expOrderIso x = exp x
  proof: rfl

中文:
引理 _root_.EReal.expOrderIso_apply
  条件: (x : E实数)
  结论: expOrderIso x = exp x
  证明: rfl
-/
@[simp] lemma _root_.EReal.expOrderIso_apply (x : EReal) : expOrderIso x = exp x := rfl

/--
lemma `logOrderIso_symm` / 引理 `logOrderIso_symm`

English:
lemma logOrderIso_symm
  statement: logOrderIso.symm = expOrderIso
  proof: rfl

中文:
引理 logOrderIso_symm
  结论: logOrderIso.symm = expOrderIso
  证明: rfl
-/
@[simp] lemma logOrderIso_symm : logOrderIso.symm = expOrderIso := rfl
/--
lemma `_root_.EReal.expOrderIso_symm` / 引理 `_root_.EReal.expOrderIso_symm`

English:
lemma _root_.EReal.expOrderIso_symm
  statement: expOrderIso.symm = logOrderIso
  proof: rfl

中文:
引理 _root_.EReal.expOrderIso_symm
  结论: expOrderIso.symm = logOrderIso
  证明: rfl
-/
@[simp] lemma _root_.EReal.expOrderIso_symm : expOrderIso.symm = logOrderIso := rfl

end OrderIso

section Continuity

/--
Definition of `logHomeomorph` / `logHomeomorph` 的定义

English:
definition logHomeomorph
  signature: : Real>=0∞ ≃ₜ EReal
  body: logOrderIso.toHomeomorph

中文:
定义 logHomeomorph
  签名: : 实数>=0∞ ≃ₜ E实数
  定义体: logOrderIso.toHomeomorph

Depends on / 依赖: logOrderIso, logOrderIso.toHomeomorph, toHomeomorph
-/
noncomputable def logHomeomorph : Real>=0∞ ≃ₜ EReal := logOrderIso.toHomeomorph

/--
lemma `logHomeomorph_apply` / 引理 `logHomeomorph_apply`

English:
lemma logHomeomorph_apply
  given: (x : Real>=0∞)
  statement: logHomeomorph x = log x
  proof: rfl

中文:
引理 logHomeomorph_apply
  条件: (x : 实数>=0∞)
  结论: logHomeomorph x = log x
  证明: rfl
-/
@[simp] lemma logHomeomorph_apply (x : Real>=0∞) : logHomeomorph x = log x := rfl

/--
Definition of `_root_.EReal.expHomeomorph` / `_root_.EReal.expHomeomorph` 的定义

English:
definition _root_.EReal.expHomeomorph
  signature: : EReal ≃ₜ Real>=0∞
  body: expOrderIso.toHomeomorph

中文:
定义 _root_.EReal.expHomeomorph
  签名: : E实数 ≃ₜ 实数>=0∞
  定义体: expOrderIso.toHomeomorph

Depends on / 依赖: expOrderIso, expOrderIso.toHomeomorph, toHomeomorph
-/
noncomputable def _root_.EReal.expHomeomorph : EReal ≃ₜ Real>=0∞ := expOrderIso.toHomeomorph

/--
lemma `_root_.EReal.expHomeomorph_apply` / 引理 `_root_.EReal.expHomeomorph_apply`

English:
lemma _root_.EReal.expHomeomorph_apply
  given: (x : EReal)
  statement: expHomeomorph x = exp x
  proof: rfl

中文:
引理 _root_.EReal.expHomeomorph_apply
  条件: (x : E实数)
  结论: expHomeomorph x = exp x
  证明: rfl
-/
@[simp] lemma _root_.EReal.expHomeomorph_apply (x : EReal) : expHomeomorph x = exp x := rfl

/--
lemma `logHomeomorph_symm` / 引理 `logHomeomorph_symm`

English:
lemma logHomeomorph_symm
  statement: logHomeomorph.symm = expHomeomorph
  proof: rfl

中文:
引理 logHomeomorph_symm
  结论: logHomeomorph.symm = expHomeomorph
  证明: rfl
-/
@[simp] lemma logHomeomorph_symm : logHomeomorph.symm = expHomeomorph := rfl

/--
lemma `_root_.EReal.expHomeomorph_symm` / 引理 `_root_.EReal.expHomeomorph_symm`

English:
lemma _root_.EReal.expHomeomorph_symm
  statement: expHomeomorph.symm = logHomeomorph
  proof: rfl

@[continuity, fun_prop]

中文:
引理 _root_.EReal.expHomeomorph_symm
  结论: expHomeomorph.symm = logHomeomorph
  证明: rfl

@[continuity, fun_prop]
-/
@[simp] lemma _root_.EReal.expHomeomorph_symm : expHomeomorph.symm = logHomeomorph := rfl

@[continuity, fun_prop]
/--
lemma `continuous_log` / 引理 `continuous_log`

English:
lemma continuous_log
  statement: Continuous log
  proof: logOrderIso.continuous

@[continuity, fun_prop]

中文:
引理 continuous_log
  结论: Continuous log
  证明: logOrderIso.continuous

@[continuity, fun_prop]

Depends on / 依赖: continuous, logOrderIso, logOrderIso.continuous
-/
lemma continuous_log : Continuous log := logOrderIso.continuous

@[continuity, fun_prop]
/--
lemma `continuous_exp` / 引理 `continuous_exp`

English:
lemma continuous_exp
  statement: Continuous exp
  proof: expOrderIso.continuous

中文:
引理 continuous_exp
  结论: Continuous exp
  证明: expOrderIso.continuous

Depends on / 依赖: continuous, expOrderIso, expOrderIso.continuous
-/
lemma continuous_exp : Continuous exp := expOrderIso.continuous

/--
lemma `_root_.EReal.tendsto_exp_nhds_top_nhds_top` / 引理 `_root_.EReal.tendsto_exp_nhds_top_nhds_top`

English:
lemma _root_.EReal.tendsto_exp_nhds_top_nhds_top
  statement: Filter.Tendsto exp (𝓝 ⊤) (𝓝 ⊤)
  proof: continuous_exp.tendsto ⊤

中文:
引理 _root_.EReal.tendsto_exp_nhds_top_nhds_top
  结论: Filter.Tendsto exp (𝓝 ⊤) (𝓝 ⊤)
  证明: continuous_exp.tendsto ⊤

Depends on / 依赖: continuous_exp, continuous_exp.tendsto, tendsto
-/
lemma _root_.EReal.tendsto_exp_nhds_top_nhds_top : Filter.Tendsto exp (𝓝 ⊤) (𝓝 ⊤) :=
  continuous_exp.tendsto ⊤

/--
lemma `_root_.EReal.tendsto_exp_nhds_zero_nhds_one` / 引理 `_root_.EReal.tendsto_exp_nhds_zero_nhds_one`

English:
lemma _root_.EReal.tendsto_exp_nhds_zero_nhds_one
  statement: Filter.Tendsto exp (𝓝 0) (𝓝 1)
  proof: by
  convert! continuous_exp.tendsto 0
  simp

中文:
引理 _root_.EReal.tendsto_exp_nhds_zero_nhds_one
  结论: Filter.Tendsto exp (𝓝 0) (𝓝 1)
  证明: by
  convert! continuous_exp.tendsto 0
  simp

Depends on / 依赖: continuous_exp, continuous_exp.tendsto, convert, tendsto
-/
lemma _root_.EReal.tendsto_exp_nhds_zero_nhds_one : Filter.Tendsto exp (𝓝 0) (𝓝 1) := by
  convert! continuous_exp.tendsto 0
  simp

/--
lemma `_root_.EReal.tendsto_exp_nhds_bot_nhds_zero` / 引理 `_root_.EReal.tendsto_exp_nhds_bot_nhds_zero`

English:
lemma _root_.EReal.tendsto_exp_nhds_bot_nhds_zero
  statement: Filter.Tendsto exp (𝓝 ⊥) (𝓝 0)
  proof: continuous_exp.tendsto ⊥

中文:
引理 _root_.EReal.tendsto_exp_nhds_bot_nhds_zero
  结论: Filter.Tendsto exp (𝓝 ⊥) (𝓝 0)
  证明: continuous_exp.tendsto ⊥

Depends on / 依赖: continuous_exp, continuous_exp.tendsto, tendsto
-/
lemma _root_.EReal.tendsto_exp_nhds_bot_nhds_zero : Filter.Tendsto exp (𝓝 ⊥) (𝓝 0) :=
  continuous_exp.tendsto ⊥

/--
lemma `tendsto_rpow_atTop_of_one_lt_base` / 引理 `tendsto_rpow_atTop_of_one_lt_base`

English:
lemma tendsto_rpow_atTop_of_one_lt_base
  given: {b : Real>=0∞} (hb : 1 < b)
  proof: by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp

中文:
引理 tendsto_rpow_atTop_of_one_lt_base
  条件: {b : 实数>=0∞} (hb : 1 < b)
  证明: by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp

Depends on / 依赖: ENNReal, ENNReal.rpow_eq_exp_mul_log, EReal.Tendsto.mul_const, EReal.tendsto_exp_nhds_top_nhds_top.comp, EReal.top_mul_of_pos, Tendsto, all_goals, convert, mul_const, rpow_eq_exp_mul_log, simp_rw, tendsto_coe_atTop, tendsto_exp_nhds_top_nhds_top, top_mul_of_pos, zero_lt_log_iff
-/
lemma tendsto_rpow_atTop_of_one_lt_base {b : Real>=0∞} (hb : 1 < b) :
    Filter.Tendsto (b ^ · : Real -> Real>=0∞) Filter.atTop (𝓝 ⊤) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp

/--
lemma `tendsto_rpow_atTop_of_base_lt_one` / 引理 `tendsto_rpow_atTop_of_base_lt_one`

English:
lemma tendsto_rpow_atTop_of_base_lt_one
  given: {b : Real>=0∞} (hb : b < 1)
  proof: by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp

中文:
引理 tendsto_rpow_atTop_of_base_lt_one
  条件: {b : 实数>=0∞} (hb : b < 1)
  证明: by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp

Depends on / 依赖: ENNReal, ENNReal.rpow_eq_exp_mul_log, EReal.Tendsto.mul_const, EReal.tendsto_exp_nhds_bot_nhds_zero.comp, EReal.top_mul_of_neg, Tendsto, all_goals, convert, log_lt_zero_iff, mul_const, rpow_eq_exp_mul_log, simp_rw, tendsto_coe_atTop, tendsto_exp_nhds_bot_nhds_zero, top_mul_of_neg
-/
lemma tendsto_rpow_atTop_of_base_lt_one {b : Real>=0∞} (hb : b < 1) :
    Filter.Tendsto (b ^ · : Real -> Real>=0∞) Filter.atTop (𝓝 0) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp

/--
lemma `tendsto_rpow_atBot_of_one_lt_base` / 引理 `tendsto_rpow_atBot_of_one_lt_base`

English:
lemma tendsto_rpow_atBot_of_one_lt_base
  given: {b : Real>=0∞} (hb : 1 < b)
  proof: by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp

中文:
引理 tendsto_rpow_atBot_of_one_lt_base
  条件: {b : 实数>=0∞} (hb : 1 < b)
  证明: by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp

Depends on / 依赖: ENNReal, ENNReal.rpow_eq_exp_mul_log, EReal.Tendsto.mul_const, EReal.bot_mul_of_pos, EReal.tendsto_exp_nhds_bot_nhds_zero.comp, Tendsto, all_goals, bot_mul_of_pos, convert, mul_const, rpow_eq_exp_mul_log, simp_rw, tendsto_coe_atBot, tendsto_exp_nhds_bot_nhds_zero, zero_lt_log_iff
-/
lemma tendsto_rpow_atBot_of_one_lt_base {b : Real>=0∞} (hb : 1 < b) :
    Filter.Tendsto (b ^ · : Real -> Real>=0∞) Filter.atBot (𝓝 0) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp

/--
lemma `tendsto_rpow_atBot_of_base_lt_one` / 引理 `tendsto_rpow_atBot_of_base_lt_one`

English:
lemma tendsto_rpow_atBot_of_base_lt_one
  given: {b : Real>=0∞} (hb : b < 1)
  proof: by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp

中文:
引理 tendsto_rpow_atBot_of_base_lt_one
  条件: {b : 实数>=0∞} (hb : b < 1)
  证明: by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp

Depends on / 依赖: ENNReal, ENNReal.rpow_eq_exp_mul_log, EReal.Tendsto.mul_const, EReal.bot_mul_of_neg, EReal.tendsto_exp_nhds_top_nhds_top.comp, Tendsto, all_goals, bot_mul_of_neg, convert, log_lt_zero_iff, mul_const, rpow_eq_exp_mul_log, simp_rw, tendsto_coe_atBot, tendsto_exp_nhds_top_nhds_top
-/
lemma tendsto_rpow_atBot_of_base_lt_one {b : Real>=0∞} (hb : b < 1) :
    Filter.Tendsto (b ^ · : Real -> Real>=0∞) Filter.atBot (𝓝 ⊤) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp

end Continuity

section Measurability

@[fun_prop]
/--
lemma `measurable_log` / 引理 `measurable_log`

English:
lemma measurable_log
  statement: Measurable log
  proof: continuous_log.measurable

@[fun_prop]

中文:
引理 measurable_log
  结论: Measurable log
  证明: continuous_log.measurable

@[fun_prop]

Depends on / 依赖: LocallyDiscrete, SmallCategory, continuous_log, continuous_log.measurable, homSmallCategory, measurable
-/
lemma measurable_log : Measurable log := continuous_log.measurable

@[fun_prop]
/--
lemma `_root_.EReal.measurable_exp` / 引理 `_root_.EReal.measurable_exp`

English:
lemma _root_.EReal.measurable_exp
  statement: Measurable exp
  proof: continuous_exp.measurable

@[fun_prop]

中文:
引理 _root_.EReal.measurable_exp
  结论: Measurable exp
  证明: continuous_exp.measurable

@[fun_prop]

Depends on / 依赖: continuous_exp, continuous_exp.measurable, measurable
-/
lemma _root_.EReal.measurable_exp : Measurable exp := continuous_exp.measurable

@[fun_prop]
/--
lemma `_root_.Measurable.ennreal_log` / 引理 `_root_.Measurable.ennreal_log`

English:
lemma _root_.Measurable.ennreal_log
  statement: {α : Type*} {_ : MeasurableSpace α}
  proof: measurable_log.comp hf

@[fun_prop]

中文:
引理 _root_.Measurable.ennreal_log
  结论: {α : 类型} {_ : MeasurableSpace α}
  证明: measurable_log.comp hf

@[fun_prop]

Depends on / 依赖: measurable_log, measurable_log.comp
-/
lemma _root_.Measurable.ennreal_log {α : Type*} {_ : MeasurableSpace α}
    {f : α -> Real>=0∞} (hf : Measurable f) :
    Measurable fun x => log (f x) := measurable_log.comp hf

@[fun_prop]
/--
lemma `_root_.Measurable.ereal_exp` / 引理 `_root_.Measurable.ereal_exp`

English:
lemma _root_.Measurable.ereal_exp
  statement: {α : Type*} {_ : MeasurableSpace α}
  proof: measurable_exp.comp hf

中文:
引理 _root_.Measurable.ereal_exp
  结论: {α : 类型} {_ : MeasurableSpace α}
  证明: measurable_exp.comp hf

Depends on / 依赖: measurable_exp, measurable_exp.comp
-/
lemma _root_.Measurable.ereal_exp {α : Type*} {_ : MeasurableSpace α}
    {f : α -> EReal} (hf : Measurable f) :
    Measurable fun x => exp (f x) := measurable_exp.comp hf

end Measurability

end ENNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PolishSpace EReal
  body: ENNReal.logOrderIso.symm.toHomeomorph.isClosedEmbedding.polishSpace

中文:
实例 :
  签名: PolishSpace E实数
  定义体: ENNReal.logOrderIso.symm.toHomeomorph.isClosedEmbedding.polishSpace

Depends on / 依赖: ENNReal, ENNReal.logOrderIso.symm.toHomeomorph.isClosedEmbedding.polishSpace, isClosedEmbedding, logOrderIso, polishSpace, toHomeomorph
-/
instance : PolishSpace EReal := ENNReal.logOrderIso.symm.toHomeomorph.isClosedEmbedding.polishSpace
