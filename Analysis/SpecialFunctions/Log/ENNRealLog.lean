/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.EReal.Basic

/-!
# Extended Nonnegative Real Logarithm

We define `log` as an extension of the logarithm of a positive real
to the extended nonnegative reals `ℝ≥0∞`. The function takes values
in the extended reals `EReal`, with `log 0 = ⊥` and `log ⊤ = ⊤`.

## Main Definitions
- `ENNReal.log`: The extension of the real logarithm to `ℝ≥0∞`.

## Main Results
- `ENNReal.log_strictMono`: `log` is increasing;
- `ENNReal.log_injective`, `ENNReal.log_surjective`, `ENNReal.log_bijective`: `log` is
  injective, surjective, and bijective;
- `ENNReal.log_mul_add`, `ENNReal.log_pow`, `ENNReal.log_rpow`: `log` satisfies
  the identities `log (x * y) = log x + log y` and `log (x ^ y) = y * log x`
  (with either `y ∈ ℕ` or `y ∈ ℝ`).

## Tags
ENNReal, EReal, logarithm
-/

@[expose] public section
namespace ENNReal

open scoped NNReal

/-! ### Definition -/
section Definition

/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: (x : Real>=0∞)
  body: if x = 0 then ⊥
    else if x = ⊤ then ⊤
    else Real.log x.toReal

中文:
定义 log
  签名: (x : 实数>=0∞)
  定义体: if x = 0 then ⊥
    else if x = ⊤ then ⊤
    else Real.log x.toReal

Depends on / 依赖: Real.log, toReal, x.toReal
-/
noncomputable def log (x : Real>=0∞) : EReal :=
  if x = 0 then ⊥
    else if x = ⊤ then ⊤
    else Real.log x.toReal

/--
lemma `log_zero` / 引理 `log_zero`

English:
lemma log_zero
  statement: log 0 = ⊥
  proof: if_pos rfl

中文:
引理 log_zero
  结论: log 0 = ⊥
  证明: if_pos rfl
-/
@[simp] lemma log_zero : log 0 = ⊥ := if_pos rfl
/--
lemma `log_one` / 引理 `log_one`

English:
lemma log_one
  statement: log 1 = 0
  proof: by simp [log]

中文:
引理 log_one
  结论: log 1 = 0
  证明: by simp [log]
-/
@[simp] lemma log_one : log 1 = 0 := by simp [log]
/--
lemma `log_top` / 引理 `log_top`

English:
lemma log_top
  statement: log ⊤ = ⊤
  proof: rfl

@[simp]

中文:
引理 log_top
  结论: log ⊤ = ⊤
  证明: rfl

@[simp]
-/
@[simp] lemma log_top : log ⊤ = ⊤ := rfl

@[simp]
/--
lemma `log_ofReal` / 引理 `log_ofReal`

English:
lemma log_ofReal
  given: (x : Real)
  statement: log (ENNReal.ofReal x) = if x <= 0 then ⊥ else ↑(Real.log x)
  proof: by
  simp only [log, ENNReal.ofReal_ne_top,
    ENNReal.ofReal_eq_zero, if_false]
  split_ifs with h_nonpos
  · rfl
  · rw [ENNReal.toReal_ofReal (not_le.mp h_nonpos).le]

中文:
引理 log_of实数
  条件: (x : 实数)
  结论: log (广义非负实数.of实数 x) = if x <= 0 then ⊥ else ↑(实数.log x)
  证明: by
  simp only [log, ENNReal.ofReal_ne_top,
    ENNReal.ofReal_eq_zero, if_false]
  split_ifs with h_nonpos
  · rfl
  · rw [ENNReal.toReal_ofReal (not_le.mp h_nonpos).le]

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal, h_nonpos, if_false, not_le, not_le.mp, ofReal_eq_zero, ofReal_ne_top, split_ifs, toReal_ofReal
-/
lemma log_ofReal (x : Real) : log (ENNReal.ofReal x) = if x <= 0 then ⊥ else ↑(Real.log x) := by
  simp only [log, ENNReal.ofReal_ne_top,
    ENNReal.ofReal_eq_zero, if_false]
  split_ifs with h_nonpos
  · rfl
  · rw [ENNReal.toReal_ofReal (not_le.mp h_nonpos).le]

/--
lemma `log_ofReal_of_pos` / 引理 `log_ofReal_of_pos`

English:
lemma log_ofReal_of_pos
  given: {x : Real} (hx : 0 < x)
  statement: log (ENNReal.ofReal x) = Real.log x
  proof: by
  rw [log_ofReal]; rw [if_neg hx.not_ge]

中文:
引理 log_of实数_of_pos
  条件: {x : 实数} (hx : 0 < x)
  结论: log (广义非负实数.of实数 x) = 实数.log x
  证明: by
  rw [log_ofReal]; rw [if_neg hx.not_ge]

Depends on / 依赖: hx.not_ge, if_neg, log_ofReal, not_ge
-/
lemma log_ofReal_of_pos {x : Real} (hx : 0 < x) : log (ENNReal.ofReal x) = Real.log x := by
  rw [log_ofReal]; rw [if_neg hx.not_ge]

/--
theorem `log_pos_real` / 定理 `log_pos_real`

English:
theorem log_pos_real
  given: {x : Real>=0∞} (h : x != 0) (h' : x != ⊤)
  proof: by simp [log, h, h']

中文:
定理 log_pos_real
  条件: {x : 实数>=0∞} (h : x != 0) (h' : x != ⊤)
  证明: by simp [log, h, h']
-/
theorem log_pos_real {x : Real>=0∞} (h : x != 0) (h' : x != ⊤) :
    log x = Real.log (ENNReal.toReal x) := by simp [log, h, h']

/--
theorem `log_pos_real'` / 定理 `log_pos_real'`

English:
theorem log_pos_real'
  given: {x : Real>=0∞} (h : 0 < x.toReal)
  proof: by
  simp [log, (ENNReal.toReal_pos_iff.1 h).1.ne', (ENNReal.toReal_pos_iff.1 h).2.ne]

中文:
定理 log_pos_real'
  条件: {x : 实数>=0∞} (h : 0 < x.to实数)
  证明: by
  simp [log, (ENNReal.toReal_pos_iff.1 h).1.ne', (ENNReal.toReal_pos_iff.1 h).2.ne]

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff, toReal_pos_iff
-/
theorem log_pos_real' {x : Real>=0∞} (h : 0 < x.toReal) :
    log x = Real.log (ENNReal.toReal x) := by
  simp [log, (ENNReal.toReal_pos_iff.1 h).1.ne', (ENNReal.toReal_pos_iff.1 h).2.ne]

/--
theorem `log_of_nnreal` / 定理 `log_of_nnreal`

English:
theorem log_of_nnreal
  given: {x : Real>=0} (h : x != 0)
  proof: by simp [log, h]

中文:
定理 log_of_nnreal
  条件: {x : 实数>=0} (h : x != 0)
  证明: by simp [log, h]
-/
theorem log_of_nnreal {x : Real>=0} (h : x != 0) :
    log (x : Real>=0∞) = Real.log x := by simp [log, h]

end Definition

/-! ### Monotonicity -/
section Monotonicity

/--
theorem `log_strictMono` / 定理 `log_strictMono`

English:
theorem log_strictMono
  statement: StrictMono log
  proof: by
  intro x y h
  unfold log
  split_ifs <;> simp_all [Real.log_lt_log, toReal_pos_iff, pos_iff_ne_zero, lt_top_iff_ne_top]

中文:
定理 log_strictMono
  结论: 严格递增 log
  证明: by
  intro x y h
  unfold log
  split_ifs <;> simp_all [Real.log_lt_log, toReal_pos_iff, pos_iff_ne_zero, lt_top_iff_ne_top]

Depends on / 依赖: Real.log_lt_log, log_lt_log, lt_top_iff_ne_top, pos_iff_ne_zero, split_ifs, toReal_pos_iff
-/
theorem log_strictMono : StrictMono log := by
  intro x y h
  unfold log
  split_ifs <;> simp_all [Real.log_lt_log, toReal_pos_iff, pos_iff_ne_zero, lt_top_iff_ne_top]

/--
theorem `log_monotone` / 定理 `log_monotone`

English:
theorem log_monotone
  statement: Monotone log
  proof: log_strictMono.monotone

中文:
定理 log_monotone
  结论: 递增 log
  证明: log_strictMono.monotone

Depends on / 依赖: log_strictMono, log_strictMono.monotone, monotone
-/
theorem log_monotone : Monotone log := log_strictMono.monotone

/--
theorem `log_injective` / 定理 `log_injective`

English:
theorem log_injective
  statement: Function.Injective log
  proof: log_strictMono.injective

中文:
定理 log_injective
  结论: 函数.单射 log
  证明: log_strictMono.injective

Depends on / 依赖: injective, log_strictMono, log_strictMono.injective
-/
theorem log_injective : Function.Injective log := log_strictMono.injective

/--
theorem `log_surjective` / 定理 `log_surjective`

English:
theorem log_surjective
  statement: Function.Surjective log
  proof: by
  intro y
  cases y with
  | bot => use 0; simp
  | top => use ⊤; simp
  | coe y => use ENNReal.ofReal (Real.exp y); simp [Real.exp_pos]

中文:
定理 log_surjective
  结论: 函数.满射 log
  证明: by
  intro y
  cases y with
  | bot => use 0; simp
  | top => use ⊤; simp
  | coe y => use ENNReal.ofReal (Real.exp y); simp [Real.exp_pos]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.exp, Real.exp_pos, cat_disch, exp_pos, ofReal
-/
theorem log_surjective : Function.Surjective log := by
  intro y
  cases y with
  | bot => use 0; simp
  | top => use ⊤; simp
  | coe y => use ENNReal.ofReal (Real.exp y); simp [Real.exp_pos]

/--
theorem `log_bijective` / 定理 `log_bijective`

English:
theorem log_bijective
  statement: Function.Bijective log
  proof: ⟨log_injective, log_surjective⟩

@[simp]

中文:
定理 log_bijective
  结论: 函数.双射 log
  证明: ⟨log_injective, log_surjective⟩

@[simp]

Depends on / 依赖: log_injective, log_surjective
-/
theorem log_bijective : Function.Bijective log := ⟨log_injective, log_surjective⟩

@[simp]
/--
theorem `log_eq_iff` / 定理 `log_eq_iff`

English:
theorem log_eq_iff
  given: {x y : Real>=0∞}
  statement: log x = log y ↔ x = y
  proof: log_injective.eq_iff

中文:
定理 log_eq_iff
  条件: {x y : 实数>=0∞}
  结论: log x = log y ↔ x = y
  证明: log_injective.eq_iff

Depends on / 依赖: eq_iff, log_injective, log_injective.eq_iff
-/
theorem log_eq_iff {x y : Real>=0∞} : log x = log y ↔ x = y :=
  log_injective.eq_iff

/--
theorem `log_eq_bot_iff` / 定理 `log_eq_bot_iff`

English:
theorem log_eq_bot_iff
  given: {x : Real>=0∞}
  statement: log x = ⊥ ↔ x = 0
  proof: log_zero ▸ @log_eq_iff x 0

中文:
定理 log_eq_bot_iff
  条件: {x : 实数>=0∞}
  结论: log x = ⊥ ↔ x = 0
  证明: log_zero ▸ @log_eq_iff x 0
-/
@[simp] theorem log_eq_bot_iff {x : Real>=0∞} : log x = ⊥ ↔ x = 0 := log_zero ▸ @log_eq_iff x 0

/--
theorem `log_eq_one_iff` / 定理 `log_eq_one_iff`

English:
theorem log_eq_one_iff
  given: {x : Real>=0∞}
  statement: log x = 0 ↔ x = 1
  proof: log_one ▸ @log_eq_iff x 1

中文:
定理 log_eq_one_iff
  条件: {x : 实数>=0∞}
  结论: log x = 0 ↔ x = 1
  证明: log_one ▸ @log_eq_iff x 1
-/
@[simp] theorem log_eq_one_iff {x : Real>=0∞} : log x = 0 ↔ x = 1 := log_one ▸ @log_eq_iff x 1

/--
theorem `log_eq_top_iff` / 定理 `log_eq_top_iff`

English:
theorem log_eq_top_iff
  given: {x : Real>=0∞}
  statement: log x = ⊤ ↔ x = ⊤
  proof: log_top ▸ @log_eq_iff x ⊤

中文:
定理 log_eq_top_iff
  条件: {x : 实数>=0∞}
  结论: log x = ⊤ ↔ x = ⊤
  证明: log_top ▸ @log_eq_iff x ⊤
-/
@[simp] theorem log_eq_top_iff {x : Real>=0∞} : log x = ⊤ ↔ x = ⊤ := log_top ▸ @log_eq_iff x ⊤

/--
lemma `log_lt_log_iff` / 引理 `log_lt_log_iff`

English:
lemma log_lt_log_iff
  given: {x y : Real>=0∞}
  statement: log x < log y ↔ x < y
  proof: log_strictMono.lt_iff_lt

中文:
引理 log_lt_log_iff
  条件: {x y : 实数>=0∞}
  结论: log x < log y ↔ x < y
  证明: log_strictMono.lt_iff_lt
-/
@[simp] lemma log_lt_log_iff {x y : Real>=0∞} : log x < log y ↔ x < y := log_strictMono.lt_iff_lt

/--
lemma `bot_lt_log_iff` / 引理 `bot_lt_log_iff`

English:
lemma bot_lt_log_iff
  given: {x : Real>=0∞}
  statement: ⊥ < log x ↔ 0 < x
  proof: log_zero ▸ @log_lt_log_iff 0 x

中文:
引理 bot_lt_log_iff
  条件: {x : 实数>=0∞}
  结论: ⊥ < log x ↔ 0 < x
  证明: log_zero ▸ @log_lt_log_iff 0 x
-/
@[simp] lemma bot_lt_log_iff {x : Real>=0∞} : ⊥ < log x ↔ 0 < x := log_zero ▸ @log_lt_log_iff 0 x

/--
lemma `log_lt_top_iff` / 引理 `log_lt_top_iff`

English:
lemma log_lt_top_iff
  given: {x : Real>=0∞}
  statement: log x < ⊤ ↔ x < ⊤
  proof: log_top ▸ @log_lt_log_iff x ⊤

中文:
引理 log_lt_top_iff
  条件: {x : 实数>=0∞}
  结论: log x < ⊤ ↔ x < ⊤
  证明: log_top ▸ @log_lt_log_iff x ⊤
-/
@[simp] lemma log_lt_top_iff {x : Real>=0∞} : log x < ⊤ ↔ x < ⊤ := log_top ▸ @log_lt_log_iff x ⊤

/--
lemma `log_lt_zero_iff` / 引理 `log_lt_zero_iff`

English:
lemma log_lt_zero_iff
  given: {x : Real>=0∞}
  statement: log x < 0 ↔ x < 1
  proof: log_one ▸ @log_lt_log_iff x 1

中文:
引理 log_lt_zero_iff
  条件: {x : 实数>=0∞}
  结论: log x < 0 ↔ x < 1
  证明: log_one ▸ @log_lt_log_iff x 1
-/
@[simp] lemma log_lt_zero_iff {x : Real>=0∞} : log x < 0 ↔ x < 1 := log_one ▸ @log_lt_log_iff x 1

/--
lemma `zero_lt_log_iff` / 引理 `zero_lt_log_iff`

English:
lemma zero_lt_log_iff
  given: {x : Real>=0∞}
  statement: 0 < log x ↔ 1 < x
  proof: log_one ▸ @log_lt_log_iff 1 x

中文:
引理 zero_lt_log_iff
  条件: {x : 实数>=0∞}
  结论: 0 < log x ↔ 1 < x
  证明: log_one ▸ @log_lt_log_iff 1 x
-/
@[simp] lemma zero_lt_log_iff {x : Real>=0∞} : 0 < log x ↔ 1 < x := log_one ▸ @log_lt_log_iff 1 x

/--
lemma `log_le_log_iff` / 引理 `log_le_log_iff`

English:
lemma log_le_log_iff
  given: {x y : Real>=0∞}
  statement: log x <= log y ↔ x <= y
  proof: log_strictMono.le_iff_le

中文:
引理 log_le_log_iff
  条件: {x y : 实数>=0∞}
  结论: log x <= log y ↔ x <= y
  证明: log_strictMono.le_iff_le
-/
@[simp] lemma log_le_log_iff {x y : Real>=0∞} : log x <= log y ↔ x <= y := log_strictMono.le_iff_le

/--
lemma `log_le_zero_iff` / 引理 `log_le_zero_iff`

English:
lemma log_le_zero_iff
  given: {x : Real>=0∞}
  statement: log x <= 0 ↔ x <= 1
  proof: log_one ▸ @log_le_log_iff x 1

中文:
引理 log_le_zero_iff
  条件: {x : 实数>=0∞}
  结论: log x <= 0 ↔ x <= 1
  证明: log_one ▸ @log_le_log_iff x 1
-/
@[simp] lemma log_le_zero_iff {x : Real>=0∞} : log x <= 0 ↔ x <= 1 := log_one ▸ @log_le_log_iff x 1

/--
lemma `zero_le_log_iff` / 引理 `zero_le_log_iff`

English:
lemma zero_le_log_iff
  given: {x : Real>=0∞}
  statement: 0 <= log x ↔ 1 <= x
  proof: log_one ▸ @log_le_log_iff 1 x

中文:
引理 zero_le_log_iff
  条件: {x : 实数>=0∞}
  结论: 0 <= log x ↔ 1 <= x
  证明: log_one ▸ @log_le_log_iff 1 x
-/
@[simp] lemma zero_le_log_iff {x : Real>=0∞} : 0 <= log x ↔ 1 <= x := log_one ▸ @log_le_log_iff 1 x

/--
lemma `log_le_log` / 引理 `log_le_log`

English:
lemma log_le_log
  given: {x y : Real>=0∞} (h : x <= y)
  statement: log x <= log y
  proof: log_monotone h

中文:
引理 log_le_log
  条件: {x y : 实数>=0∞} (h : x <= y)
  结论: log x <= log y
  证明: log_monotone h

Depends on / 依赖: cat_disch
-/
@[gcongr] lemma log_le_log {x y : Real>=0∞} (h : x <= y) : log x <= log y := log_monotone h
/--
lemma `log_lt_log` / 引理 `log_lt_log`

English:
lemma log_lt_log
  given: {x y : Real>=0∞} (h : x < y)
  statement: log x < log y
  proof: log_strictMono h

中文:
引理 log_lt_log
  条件: {x y : 实数>=0∞} (h : x < y)
  结论: log x < log y
  证明: log_strictMono h
-/
@[gcongr] lemma log_lt_log {x y : Real>=0∞} (h : x < y) : log x < log y := log_strictMono h

end Monotonicity

/-! ### Algebraic properties -/

section Morphism

/--
theorem `log_mul_add` / 定理 `log_mul_add`

English:
theorem log_mul_add
  given: {x y : Real>=0∞}
  statement: log (x * y) = log x + log y
  proof: by
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · simp
  · rw [log_top]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · rw [mul_zero, log_zero, EReal.add_bot]
    · simp
    · rw [log_pos_real' y_real, ENNReal.top_mul', EReal.top_add_coe, log_eq_top_iff]
      simp only [ite_eq_right_iff, zero_ne_top, imp_false]
      exact (ENNReal.toReal_pos_iff.1 y_real).1.ne'
  · rw [log_pos_real' x_real]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · simp
    · simp [(ENNReal.toReal_pos_iff.1 x_real).1.ne']
    · rw_mod_cast [log_pos_real', log_pos_real' y_real, ENNReal.toReal_mul]
      · exact Real.log_mul x_real.ne' y_real.ne'
      rw [toReal_mul]
      positivity

中文:
定理 log_mul_add
  条件: {x y : 实数>=0∞}
  结论: log (x * y) = log x + log y
  证明: by
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · simp
  · rw [log_top]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · rw [mul_zero, log_zero, EReal.add_bot]
    · simp
    · rw [log_pos_real' y_real, ENNReal.top_mul', EReal.top_add_coe, log_eq_top_iff]
      simp only [ite_eq_right_iff, zero_ne_top, imp_false]
      exact (ENNReal.toReal_pos_iff.1 y_real).1.ne'
  · rw [log_pos_real' x_real]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · simp
    · simp [(ENNReal.toReal_pos_iff.1 x_real).1.ne']
    · rw_mod_cast [log_pos_real', log_pos_real' y_real, ENNReal.toReal_mul]
      · exact Real.log_mul x_real.ne' y_real.ne'
      rw [toReal_mul]
      positivity

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff, ENNReal.top_mul, ENNReal.trichotomy, EReal.add_bot, EReal.top_add_coe, add_bot, imp_false, ite_eq_right_iff, log_eq_top_iff, log_pos_real, log_top, log_zero, mul_zero, toReal_pos_iff, top_add_coe, top_mul, trichotomy, x_real, y_real
-/
theorem log_mul_add {x y : Real>=0∞} : log (x * y) = log x + log y := by
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · simp
  · rw [log_top]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · rw [mul_zero, log_zero, EReal.add_bot]
    · simp
    · rw [log_pos_real' y_real, ENNReal.top_mul', EReal.top_add_coe, log_eq_top_iff]
      simp only [ite_eq_right_iff, zero_ne_top, imp_false]
      exact (ENNReal.toReal_pos_iff.1 y_real).1.ne'
  · rw [log_pos_real' x_real]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · simp
    · simp [(ENNReal.toReal_pos_iff.1 x_real).1.ne']
    · rw_mod_cast [log_pos_real', log_pos_real' y_real, ENNReal.toReal_mul]
      · exact Real.log_mul x_real.ne' y_real.ne'
      rw [toReal_mul]
      positivity

/--
theorem `log_rpow` / 定理 `log_rpow`

English:
theorem log_rpow
  given: {x : Real>=0∞} {y : Real}
  statement: log (x ^ y) = y * log x
  proof: by
  rcases lt_trichotomy y 0 with (y_neg | rfl | y_pos)
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · simp only [ENNReal.zero_rpow_def y, not_lt_of_gt y_neg, y_neg.ne, if_false, log_top,
        log_zero, EReal.coe_mul_bot_of_neg y_neg]
    · rw [ENNReal.top_rpow_of_neg y_neg, log_zero, log_top, EReal.coe_mul_top_of_neg y_neg]
    · have x_ne_zero := (ENNReal.toReal_pos_iff.1 x_real).1.ne'
      have x_ne_top := (ENNReal.toReal_pos_iff.1 x_real).2.ne
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y
  · simp
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · rw [ENNReal.zero_rpow_of_pos y_pos, log_zero, EReal.mul_bot_of_pos]; norm_cast
    · rw [ENNReal.top_rpow_of_pos y_pos, log_top, EReal.mul_top_of_pos]; norm_cast
    · have x_ne_zero := (ENNReal.toReal_pos_iff.1 x_real).1.ne'
      have x_ne_top := (ENNReal.toReal_pos_iff.1 x_real).2.ne
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y

中文:
定理 log_rpow
  条件: {x : 实数>=0∞} {y : 实数}
  结论: log (x ^ y) = y * log x
  证明: by
  rcases lt_trichotomy y 0 with (y_neg | rfl | y_pos)
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · simp only [ENNReal.zero_rpow_def y, not_lt_of_gt y_neg, y_neg.ne, if_false, log_top,
        log_zero, EReal.coe_mul_bot_of_neg y_neg]
    · rw [ENNReal.top_rpow_of_neg y_neg, log_zero, log_top, EReal.coe_mul_top_of_neg y_neg]
    · have x_ne_zero := (ENNReal.toReal_pos_iff.1 x_real).1.ne'
      have x_ne_top := (ENNReal.toReal_pos_iff.1 x_real).2.ne
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y
  · simp
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · rw [ENNReal.zero_rpow_of_pos y_pos, log_zero, EReal.mul_bot_of_pos]; norm_cast
    · rw [ENNReal.top_rpow_of_pos y_pos, log_top, EReal.mul_top_of_pos]; norm_cast
    · have x_ne_zero := (ENNReal.toReal_pos_iff.1 x_real).1.ne'
      have x_ne_top := (ENNReal.toReal_pos_iff.1 x_real).2.ne
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff, ENNReal.top_rpow_of_neg, ENNReal.trichotomy, ENNReal.zero_rpow_def, EReal.coe_mul_bot_of_neg, EReal.coe_mul_top_of_neg, coe_mul_bot_of_neg, coe_mul_top_of_neg, false_and, if_false, log_top, log_zero, lt_trichotomy, not_lt_of_gt, rpow_eq_zero_iff, toReal_pos_iff, top_rpow_of_neg, trichotomy, x_ne_top
-/
theorem log_rpow {x : Real>=0∞} {y : Real} : log (x ^ y) = y * log x := by
  rcases lt_trichotomy y 0 with (y_neg | rfl | y_pos)
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · simp only [ENNReal.zero_rpow_def y, not_lt_of_gt y_neg, y_neg.ne, if_false, log_top,
        log_zero, EReal.coe_mul_bot_of_neg y_neg]
    · rw [ENNReal.top_rpow_of_neg y_neg, log_zero, log_top, EReal.coe_mul_top_of_neg y_neg]
    · have x_ne_zero := (ENNReal.toReal_pos_iff.1 x_real).1.ne'
      have x_ne_top := (ENNReal.toReal_pos_iff.1 x_real).2.ne
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y
  · simp
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · rw [ENNReal.zero_rpow_of_pos y_pos, log_zero, EReal.mul_bot_of_pos]; norm_cast
    · rw [ENNReal.top_rpow_of_pos y_pos, log_top, EReal.mul_top_of_pos]; norm_cast
    · have x_ne_zero := (ENNReal.toReal_pos_iff.1 x_real).1.ne'
      have x_ne_top := (ENNReal.toReal_pos_iff.1 x_real).2.ne
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y

/--
theorem `log_pow` / 定理 `log_pow`

English:
theorem log_pow
  given: {x : Real>=0∞} {n : Nat}
  statement: log (x ^ n) = n * log x
  proof: by
  rw [← rpow_natCast]; rw [log_rpow]; rw [EReal.coe_natCast]

中文:
定理 log_pow
  条件: {x : 实数>=0∞} {n : 自然数}
  结论: log (x ^ n) = n * log x
  证明: by
  rw [← rpow_natCast]; rw [log_rpow]; rw [EReal.coe_natCast]

Depends on / 依赖: EReal.coe_natCast, coe_natCast, log_rpow, rpow_natCast
-/
theorem log_pow {x : Real>=0∞} {n : Nat} : log (x ^ n) = n * log x := by
  rw [← rpow_natCast]; rw [log_rpow]; rw [EReal.coe_natCast]

/--
lemma `log_inv` / 引理 `log_inv`

English:
lemma log_inv
  given: {x : Real>=0∞}
  statement: log x⁻¹ = - log x
  proof: by
  simp [← rpow_neg_one, log_rpow]

中文:
引理 log_inv
  条件: {x : 实数>=0∞}
  结论: log x⁻¹ = - log x
  证明: by
  simp [← rpow_neg_one, log_rpow]

Depends on / 依赖: log_rpow, rpow_neg_one
-/
lemma log_inv {x : Real>=0∞} : log x⁻¹ = - log x := by
  simp [← rpow_neg_one, log_rpow]

end Morphism

end ENNReal
