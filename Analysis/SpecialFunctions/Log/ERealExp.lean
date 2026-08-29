/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.EReal.Basic

/-!
# Extended Nonnegative Real Exponential

We define `exp` as an extension of the exponential of a real
to the extended reals `EReal`. The function takes values
in the extended nonnegative reals `ℝ≥0∞`, with `exp ⊥ = 0` and `exp ⊤ = ⊤`.

## Main Definitions
- `EReal.exp`: The extension of the real exponential to `EReal`.

## Main Results
- `EReal.exp_strictMono`: `exp` is increasing;
- `EReal.exp_neg`, `EReal.exp_add`: `exp` satisfies
  the identities `exp (-x) = (exp x)⁻¹` and `exp (x + y) = exp x * exp y`.

## Tags
ENNReal, EReal, exponential
-/

@[expose] public section
namespace EReal

open scoped ENNReal

/-! ### Definition -/
section Definition

/-- Exponential as a function from `EReal` to `ℝ≥0∞`. -/
noncomputable
/--
Definition of `exp` / `exp` 的定义

English:
definition exp
  signature: (x : EReal)
  body: EReal.rec 0 (fun x => ENNReal.ofReal (Real.exp x)) ∞ x

中文:
定义 exp
  签名: (x : E实数)
  定义体: EReal.rec 0 (fun x => ENNReal.ofReal (Real.exp x)) ∞ x

Depends on / 依赖: ENNReal, ENNReal.ofReal, EReal.rec, Real.exp, ofReal
-/
def exp (x : EReal) : Real>=0∞ := EReal.rec 0 (fun x => ENNReal.ofReal (Real.exp x)) ∞ x

/--
lemma `exp_bot` / 引理 `exp_bot`

English:
lemma exp_bot
  statement: exp ⊥ = 0
  proof: rfl

中文:
引理 exp_bot
  结论: exp ⊥ = 0
  证明: rfl

Depends on / 依赖: Discrete, Discrete.isDiscrete, isDiscrete
-/
@[simp] lemma exp_bot : exp ⊥ = 0 := rfl
/--
lemma `exp_zero` / 引理 `exp_zero`

English:
lemma exp_zero
  statement: exp 0 = 1
  proof: by simp [exp, ← coe_zero]

中文:
引理 exp_zero
  结论: exp 0 = 1
  证明: by simp [exp, ← coe_zero]

Depends on / 依赖: leftUnitor, obj_ext_of_isDiscrete
-/
@[simp] lemma exp_zero : exp 0 = 1 := by simp [exp, ← coe_zero]
/--
lemma `exp_top` / 引理 `exp_top`

English:
lemma exp_top
  statement: exp ⊤ = ∞
  proof: rfl

中文:
引理 exp_top
  结论: exp ⊤ = ∞
  证明: rfl
-/
@[simp] lemma exp_top : exp ⊤ = ∞ := rfl
/--
lemma `exp_coe` / 引理 `exp_coe`

English:
lemma exp_coe
  given: (x : Real)
  statement: exp x = ENNReal.ofReal (Real.exp x)
  proof: rfl

中文:
引理 exp_coe
  条件: (x : 实数)
  结论: exp x = 广义非负实数.of实数 (实数.exp x)
  证明: rfl
-/
@[simp] lemma exp_coe (x : Real) : exp x = ENNReal.ofReal (Real.exp x) := rfl

/--
lemma `exp_eq_zero_iff` / 引理 `exp_eq_zero_iff`

English:
lemma exp_eq_zero_iff
  given: {x : EReal}
  statement: exp x = 0 ↔ x = ⊥
  proof: by
  induction x <;> simp [Real.exp_pos]

中文:
引理 exp_eq_zero_iff
  条件: {x : E实数}
  结论: exp x = 0 ↔ x = ⊥
  证明: by
  induction x <;> simp [Real.exp_pos]
-/
@[simp] lemma exp_eq_zero_iff {x : EReal} : exp x = 0 ↔ x = ⊥ := by
  induction x <;> simp [Real.exp_pos]

/--
lemma `exp_eq_top_iff` / 引理 `exp_eq_top_iff`

English:
lemma exp_eq_top_iff
  given: {x : EReal}
  statement: exp x = ∞ ↔ x = ⊤
  proof: by
  induction x <;> simp

中文:
引理 exp_eq_top_iff
  条件: {x : E实数}
  结论: exp x = ∞ ↔ x = ⊤
  证明: by
  induction x <;> simp
-/
@[simp] lemma exp_eq_top_iff {x : EReal} : exp x = ∞ ↔ x = ⊤ := by
  induction x <;> simp

end Definition

/-! ### Monotonicity -/
section Monotonicity

@[gcongr]
/--
lemma `exp_strictMono` / 引理 `exp_strictMono`

English:
lemma exp_strictMono
  statement: StrictMono exp
  proof: by
  intro x y h
  induction x
  · rw [exp_bot, pos_iff_ne_zero, ne_eq, exp_eq_zero_iff]
    exact h.ne'
  · induction y
    · simp at h
    · simp_rw [exp_coe]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨Real.exp_strictMono (mod_cast h), Real.exp_pos _⟩
    · simp
  · exact (not_top_lt h).elim

@[gcongr]

中文:
引理 exp_strictMono
  结论: 严格递增 exp
  证明: by
  intro x y h
  induction x
  · rw [exp_bot, pos_iff_ne_zero, ne_eq, exp_eq_zero_iff]
    exact h.ne'
  · induction y
    · simp at h
    · simp_rw [exp_coe]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨Real.exp_strictMono (mod_cast h), Real.exp_pos _⟩
    · simp
  · exact (not_top_lt h).elim

@[gcongr]

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_ofReal_iff, Real.exp_pos, Real.exp_strictMono, exp_bot, exp_coe, exp_eq_zero_iff, exp_pos, exp_strictMono, h.ne, mod_cast, ne_eq, not_top_lt, ofReal_lt_ofReal_iff, pos_iff_ne_zero, simp_rw
-/
lemma exp_strictMono : StrictMono exp := by
  intro x y h
  induction x
  · rw [exp_bot, pos_iff_ne_zero, ne_eq, exp_eq_zero_iff]
    exact h.ne'
  · induction y
    · simp at h
    · simp_rw [exp_coe]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨Real.exp_strictMono (mod_cast h), Real.exp_pos _⟩
    · simp
  · exact (not_top_lt h).elim

@[gcongr]
/--
lemma `exp_monotone` / 引理 `exp_monotone`

English:
lemma exp_monotone
  statement: Monotone exp
  proof: exp_strictMono.monotone

中文:
引理 exp_monotone
  结论: 递增 exp
  证明: exp_strictMono.monotone

Depends on / 依赖: exp_strictMono, exp_strictMono.monotone, monotone
-/
lemma exp_monotone : Monotone exp := exp_strictMono.monotone

/--
lemma `exp_lt_exp_iff` / 引理 `exp_lt_exp_iff`

English:
lemma exp_lt_exp_iff
  given: {a b : EReal}
  statement: exp a < exp b ↔ a < b
  proof: exp_strictMono.lt_iff_lt

中文:
引理 exp_lt_exp_iff
  条件: {a b : E实数}
  结论: exp a < exp b ↔ a < b
  证明: exp_strictMono.lt_iff_lt
-/
@[simp] lemma exp_lt_exp_iff {a b : EReal} : exp a < exp b ↔ a < b := exp_strictMono.lt_iff_lt

/--
lemma `zero_lt_exp_iff` / 引理 `zero_lt_exp_iff`

English:
lemma zero_lt_exp_iff
  given: {a : EReal}
  statement: 0 < exp a ↔ ⊥ < a
  proof: exp_bot ▸ @exp_lt_exp_iff ⊥ a

中文:
引理 zero_lt_exp_iff
  条件: {a : E实数}
  结论: 0 < exp a ↔ ⊥ < a
  证明: exp_bot ▸ @exp_lt_exp_iff ⊥ a
-/
@[simp] lemma zero_lt_exp_iff {a : EReal} : 0 < exp a ↔ ⊥ < a := exp_bot ▸ @exp_lt_exp_iff ⊥ a

/--
lemma `exp_lt_top_iff` / 引理 `exp_lt_top_iff`

English:
lemma exp_lt_top_iff
  given: {a : EReal}
  statement: exp a < ⊤ ↔ a < ⊤
  proof: exp_top ▸ @exp_lt_exp_iff a ⊤

中文:
引理 exp_lt_top_iff
  条件: {a : E实数}
  结论: exp a < ⊤ ↔ a < ⊤
  证明: exp_top ▸ @exp_lt_exp_iff a ⊤
-/
@[simp] lemma exp_lt_top_iff {a : EReal} : exp a < ⊤ ↔ a < ⊤ := exp_top ▸ @exp_lt_exp_iff a ⊤

/--
lemma `exp_lt_one_iff` / 引理 `exp_lt_one_iff`

English:
lemma exp_lt_one_iff
  given: {a : EReal}
  statement: exp a < 1 ↔ a < 0
  proof: exp_zero ▸ @exp_lt_exp_iff a 0

中文:
引理 exp_lt_one_iff
  条件: {a : E实数}
  结论: exp a < 1 ↔ a < 0
  证明: exp_zero ▸ @exp_lt_exp_iff a 0
-/
@[simp] lemma exp_lt_one_iff {a : EReal} : exp a < 1 ↔ a < 0 := exp_zero ▸ @exp_lt_exp_iff a 0

/--
lemma `one_lt_exp_iff` / 引理 `one_lt_exp_iff`

English:
lemma one_lt_exp_iff
  given: {a : EReal}
  statement: 1 < exp a ↔ 0 < a
  proof: exp_zero ▸ @exp_lt_exp_iff 0 a

中文:
引理 one_lt_exp_iff
  条件: {a : E实数}
  结论: 1 < exp a ↔ 0 < a
  证明: exp_zero ▸ @exp_lt_exp_iff 0 a
-/
@[simp] lemma one_lt_exp_iff {a : EReal} : 1 < exp a ↔ 0 < a := exp_zero ▸ @exp_lt_exp_iff 0 a

/--
lemma `exp_le_exp_iff` / 引理 `exp_le_exp_iff`

English:
lemma exp_le_exp_iff
  given: {a b : EReal}
  statement: exp a <= exp b ↔ a <= b
  proof: exp_strictMono.le_iff_le

中文:
引理 exp_le_exp_iff
  条件: {a b : E实数}
  结论: exp a <= exp b ↔ a <= b
  证明: exp_strictMono.le_iff_le
-/
@[simp] lemma exp_le_exp_iff {a b : EReal} : exp a <= exp b ↔ a <= b := exp_strictMono.le_iff_le

/--
lemma `exp_le_one_iff` / 引理 `exp_le_one_iff`

English:
lemma exp_le_one_iff
  given: {a : EReal}
  statement: exp a <= 1 ↔ a <= 0
  proof: exp_zero ▸ @exp_le_exp_iff a 0

中文:
引理 exp_le_one_iff
  条件: {a : E实数}
  结论: exp a <= 1 ↔ a <= 0
  证明: exp_zero ▸ @exp_le_exp_iff a 0
-/
@[simp] lemma exp_le_one_iff {a : EReal} : exp a <= 1 ↔ a <= 0 := exp_zero ▸ @exp_le_exp_iff a 0

/--
lemma `one_le_exp_iff` / 引理 `one_le_exp_iff`

English:
lemma one_le_exp_iff
  given: {a : EReal}
  statement: 1 <= exp a ↔ 0 <= a
  proof: exp_zero ▸ @exp_le_exp_iff 0 a

中文:
引理 one_le_exp_iff
  条件: {a : E实数}
  结论: 1 <= exp a ↔ 0 <= a
  证明: exp_zero ▸ @exp_le_exp_iff 0 a
-/
@[simp] lemma one_le_exp_iff {a : EReal} : 1 <= exp a ↔ 0 <= a := exp_zero ▸ @exp_le_exp_iff 0 a

end Monotonicity

/-! ### Algebraic properties -/

section Morphism

/--
lemma `exp_neg` / 引理 `exp_neg`

English:
lemma exp_neg
  given: (x : EReal)
  statement: exp (-x) = (exp x)⁻¹
  proof: by
  induction x
  · simp
  · rw [exp_coe, ← EReal.coe_neg, exp_coe, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
      Real.exp_neg]
  · simp

中文:
引理 exp_neg
  条件: (x : E实数)
  结论: exp (-x) = (exp x)⁻¹
  证明: by
  induction x
  · simp
  · rw [exp_coe, ← EReal.coe_neg, exp_coe, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
      Real.exp_neg]
  · simp

Depends on / 依赖: ENNReal, ENNReal.ofReal_inv_of_pos, EReal.coe_neg, Real.exp_neg, Real.exp_pos, coe_neg, exp_coe, exp_neg, exp_pos, ofReal_inv_of_pos
-/
lemma exp_neg (x : EReal) : exp (-x) = (exp x)⁻¹ := by
  induction x
  · simp
  · rw [exp_coe, ← EReal.coe_neg, exp_coe, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
      Real.exp_neg]
  · simp

/--
lemma `exp_add` / 引理 `exp_add`

English:
lemma exp_add
  given: (x y : EReal)
  statement: exp (x + y) = exp x * exp y
  proof: by
  induction x
  · simp
  · induction y
    · simp
    · simp only [← EReal.coe_add, exp_coe]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]; rw [Real.exp_add]
    · simp only [EReal.coe_add_top, exp_top, exp_coe]
      rw [ENNReal.mul_top]
      simp [Real.exp_pos]
  · induction y
    · simp
    · simp only [EReal.top_add_coe, exp_top, exp_coe]
      rw [ENNReal.top_mul]
      simp [Real.exp_pos]
    · simp

中文:
引理 exp_add
  条件: (x y : E实数)
  结论: exp (x + y) = exp x * exp y
  证明: by
  induction x
  · simp
  · induction y
    · simp
    · simp only [← EReal.coe_add, exp_coe]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]; rw [Real.exp_add]
    · simp only [EReal.coe_add_top, exp_top, exp_coe]
      rw [ENNReal.mul_top]
      simp [Real.exp_pos]
  · induction y
    · simp
    · simp only [EReal.top_add_coe, exp_top, exp_coe]
      rw [ENNReal.top_mul]
      simp [Real.exp_pos]
    · simp

Depends on / 依赖: ENNReal, ENNReal.mul_top, ENNReal.ofReal_mul, ENNReal.top_mul, EReal.coe_add, EReal.coe_add_top, EReal.top_add_coe, Real.exp_add, Real.exp_nonneg, Real.exp_pos, coe_add, coe_add_top, exp_add, exp_coe, exp_nonneg, exp_pos, exp_top, mul_top, ofReal_mul, top_add_coe
-/
lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y := by
  induction x
  · simp
  · induction y
    · simp
    · simp only [← EReal.coe_add, exp_coe]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]; rw [Real.exp_add]
    · simp only [EReal.coe_add_top, exp_top, exp_coe]
      rw [ENNReal.mul_top]
      simp [Real.exp_pos]
  · induction y
    · simp
    · simp only [EReal.top_add_coe, exp_top, exp_coe]
      rw [ENNReal.top_mul]
      simp [Real.exp_pos]
    · simp

end Morphism

end EReal
