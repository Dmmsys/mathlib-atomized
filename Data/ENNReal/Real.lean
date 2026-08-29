/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.ENNReal.Basic

/-!
# Maps between real and extended non-negative real numbers

This file focuses on the functions `ENNReal.toReal : ℝ≥0∞ → ℝ` and `ENNReal.ofReal : ℝ → ℝ≥0∞` which
were defined in `Data.ENNReal.Basic`. It collects all the basic results of the interactions between
these functions and the algebraic and lattice operations, although a few may appear in earlier
files.

This file provides a `positivity` extension for `ENNReal.ofReal`.

## Main statements

  - `trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal`: often used for `WithLp` and `lp`
  - `dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal`: often used for `WithLp` and `lp`
  - `toNNReal_iInf` through `toReal_sSup`: these declarations allow for easy conversions between
    indexed or set infima and suprema in `ℝ`, `ℝ≥0` and `ℝ≥0∞`. This is especially useful because
    `ℝ≥0∞` is a complete lattice.
-/

@[expose] public section

assert_not_exists Finset

open Set NNReal ENNReal

namespace ENNReal

section Real

variable {a b c d : Real>=0∞} {r p q : Real>=0}

/--
theorem `toReal_add` / 定理 `toReal_add`

English:
theorem toReal_add
  given: (ha : a != ∞) (hb : b != ∞)
  statement: (a + b).toReal = a.toReal + b.toReal
  proof: by
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  rfl

中文:
定理 toReal_add
  条件: (ha : a != ∞) (hb : b != ∞)
  结论: (a + b).to实数 = a.to实数 + b.to实数
  证明: by
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  rfl
-/
theorem toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toReal = a.toReal + b.toReal := by
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  rfl

/--
theorem `toReal_add_le` / 定理 `toReal_add_le`

English:
theorem toReal_add_le
  statement: (a + b).toReal <= a.toReal + b.toReal
  proof: if ha : a = ∞ then by simp only [ha, top_add, toReal_top, zero_add, toReal_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, toReal_top, add_zero, toReal_nonneg]
    else le_of_eq (toReal_add ha hb)

中文:
定理 toReal_add_le
  结论: (a + b).to实数 <= a.to实数 + b.to实数
  证明: if ha : a = ∞ then by simp only [ha, top_add, toReal_top, zero_add, toReal_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, toReal_top, add_zero, toReal_nonneg]
    else le_of_eq (toReal_add ha hb)

Depends on / 依赖: add_top, add_zero, le_of_eq, toReal_add, toReal_nonneg, toReal_top, top_add, zero_add
-/
theorem toReal_add_le : (a + b).toReal <= a.toReal + b.toReal :=
  if ha : a = ∞ then by simp only [ha, top_add, toReal_top, zero_add, toReal_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, toReal_top, add_zero, toReal_nonneg]
    else le_of_eq (toReal_add ha hb)

/--
theorem `ofReal_add` / 定理 `ofReal_add`

English:
theorem ofReal_add
  given: {p q : Real} (hp : 0 <= p) (hq : 0 <= q)
  proof: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [← coe_add]; rw [coe_inj]; rw [Real.toNNReal_add hp hq]

中文:
定理 ofReal_add
  条件: {p q : 实数} (hp : 0 <= p) (hq : 0 <= q)
  证明: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [← coe_add]; rw [coe_inj]; rw [Real.toNNReal_add hp hq]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_add, coe_add, coe_inj, ofReal, toNNReal_add
-/
theorem ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) :
    ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q := by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [← coe_add]; rw [coe_inj]; rw [Real.toNNReal_add hp hq]

/--
theorem `ofReal_add_le` / 定理 `ofReal_add_le`

English:
theorem ofReal_add_le
  given: {p q : Real}
  statement: ENNReal.ofReal (p + q) <= ENNReal.ofReal p + ENNReal.ofReal q
  proof: coe_le_coe.2 Real.toNNReal_add_le

@[simp]

中文:
定理 ofReal_add_le
  条件: {p q : 实数}
  结论: ENN实数.of实数 (p + q) <= ENN实数.of实数 p + ENN实数.of实数 q
  证明: coe_le_coe.2 Real.toNNReal_add_le

@[simp]

Depends on / 依赖: Real.toNNReal_add_le, coe_le_coe, toNNReal_add_le
-/
theorem ofReal_add_le {p q : Real} : ENNReal.ofReal (p + q) <= ENNReal.ofReal p + ENNReal.ofReal q :=
  coe_le_coe.2 Real.toNNReal_add_le

@[simp]
/--
theorem `toReal_le_toReal` / 定理 `toReal_le_toReal`

English:
theorem toReal_le_toReal
  given: (ha : a != ∞) (hb : b != ∞)
  statement: a.toReal <= b.toReal ↔ a <= b
  proof: by
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  norm_cast

@[gcongr]

中文:
定理 toReal_le_toReal
  条件: (ha : a != ∞) (hb : b != ∞)
  结论: a.to实数 <= b.to实数 ↔ a <= b
  证明: by
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  norm_cast

@[gcongr]
-/
theorem toReal_le_toReal (ha : a != ∞) (hb : b != ∞) : a.toReal <= b.toReal ↔ a <= b := by
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  norm_cast

@[gcongr]
/--
theorem `toReal_mono` / 定理 `toReal_mono`

English:
theorem toReal_mono
  given: (hb : b != ∞) (h : a <= b)
  statement: a.toReal <= b.toReal
  proof: (toReal_le_toReal (ne_top_of_le_ne_top hb h) hb).2 h

中文:
定理 toReal_mono
  条件: (hb : b != ∞) (h : a <= b)
  结论: a.to实数 <= b.to实数
  证明: (toReal_le_toReal (ne_top_of_le_ne_top hb h) hb).2 h

Depends on / 依赖: ne_top_of_le_ne_top, toReal_le_toReal
-/
theorem toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <= b.toReal :=
  (toReal_le_toReal (ne_top_of_le_ne_top hb h) hb).2 h

/--
theorem `toReal_mono'` / 定理 `toReal_mono'`

English:
theorem toReal_mono'
  given: (h : a <= b) (ht : b = ∞ -> a = ∞)
  statement: a.toReal <= b.toReal
  proof: by
  rcases eq_or_ne a ∞ with rfl | ha
  · exact toReal_nonneg
  · exact toReal_mono (mt ht ha) h

@[simp]

中文:
定理 toReal_mono'
  条件: (h : a <= b) (ht : b = ∞ -> a = ∞)
  结论: a.to实数 <= b.to实数
  证明: by
  rcases eq_or_ne a ∞ with rfl | ha
  · exact toReal_nonneg
  · exact toReal_mono (mt ht ha) h

@[simp]

Depends on / 依赖: eq_or_ne, toReal_mono, toReal_nonneg
-/
theorem toReal_mono' (h : a <= b) (ht : b = ∞ -> a = ∞) : a.toReal <= b.toReal := by
  rcases eq_or_ne a ∞ with rfl | ha
  · exact toReal_nonneg
  · exact toReal_mono (mt ht ha) h

@[simp]
/--
theorem `toReal_lt_toReal` / 定理 `toReal_lt_toReal`

English:
theorem toReal_lt_toReal
  given: (ha : a != ∞) (hb : b != ∞)
  statement: a.toReal < b.toReal ↔ a < b
  proof: by
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  norm_cast

@[gcongr]

中文:
定理 toReal_lt_toReal
  条件: (ha : a != ∞) (hb : b != ∞)
  结论: a.to实数 < b.to实数 ↔ a < b
  证明: by
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  norm_cast

@[gcongr]
-/
theorem toReal_lt_toReal (ha : a != ∞) (hb : b != ∞) : a.toReal < b.toReal ↔ a < b := by
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  norm_cast

@[gcongr]
/--
theorem `toReal_strict_mono` / 定理 `toReal_strict_mono`

English:
theorem toReal_strict_mono
  given: (hb : b != ∞) (h : a < b)
  statement: a.toReal < b.toReal
  proof: (toReal_lt_toReal h.ne_top hb).2 h

@[gcongr]

中文:
定理 toReal_strict_mono
  条件: (hb : b != ∞) (h : a < b)
  结论: a.to实数 < b.to实数
  证明: (toReal_lt_toReal h.ne_top hb).2 h

@[gcongr]

Depends on / 依赖: h.ne_top, ne_top, toReal_lt_toReal
-/
theorem toReal_strict_mono (hb : b != ∞) (h : a < b) : a.toReal < b.toReal :=
  (toReal_lt_toReal h.ne_top hb).2 h

@[gcongr]
/--
theorem `toNNReal_mono` / 定理 `toNNReal_mono`

English:
theorem toNNReal_mono
  given: (hb : b != ∞) (h : a <= b)
  statement: a.toNNReal <= b.toNNReal
  proof: toReal_mono hb h

中文:
定理 toNNReal_mono
  条件: (hb : b != ∞) (h : a <= b)
  结论: a.toNN实数 <= b.toNN实数
  证明: toReal_mono hb h

Depends on / 依赖: toReal_mono
-/
theorem toNNReal_mono (hb : b != ∞) (h : a <= b) : a.toNNReal <= b.toNNReal :=
  toReal_mono hb h

/--
theorem `le_toNNReal_of_coe_le` / 定理 `le_toNNReal_of_coe_le`

English:
theorem le_toNNReal_of_coe_le
  given: (h : p <= a) (ha : a != ∞)
  statement: p <= a.toNNReal
  proof: @toNNReal_coe p ▸ toNNReal_mono ha h

@[simp]

中文:
定理 le_toNNReal_of_coe_le
  条件: (h : p <= a) (ha : a != ∞)
  结论: p <= a.toNN实数
  证明: @toNNReal_coe p ▸ toNNReal_mono ha h

@[simp]

Depends on / 依赖: toNNReal_coe, toNNReal_mono
-/
theorem le_toNNReal_of_coe_le (h : p <= a) (ha : a != ∞) : p <= a.toNNReal :=
  @toNNReal_coe p ▸ toNNReal_mono ha h

@[simp]
/--
theorem `toNNReal_le_toNNReal` / 定理 `toNNReal_le_toNNReal`

English:
theorem toNNReal_le_toNNReal
  given: (ha : a != ∞) (hb : b != ∞)
  statement: a.toNNReal <= b.toNNReal ↔ a <= b
  proof: ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_le_coe], toNNReal_mono hb⟩

@[gcongr]

中文:
定理 toNNReal_le_toNNReal
  条件: (ha : a != ∞) (hb : b != ∞)
  结论: a.toNN实数 <= b.toNN实数 ↔ a <= b
  证明: ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_le_coe], toNNReal_mono hb⟩

@[gcongr]

Depends on / 依赖: coe_le_coe, coe_toNNReal, toNNReal_mono
-/
theorem toNNReal_le_toNNReal (ha : a != ∞) (hb : b != ∞) : a.toNNReal <= b.toNNReal ↔ a <= b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_le_coe], toNNReal_mono hb⟩

@[gcongr]
/--
theorem `toNNReal_strict_mono` / 定理 `toNNReal_strict_mono`

English:
theorem toNNReal_strict_mono
  given: (hb : b != ∞) (h : a < b)
  statement: a.toNNReal < b.toNNReal
  proof: by
  simpa [← ENNReal.coe_lt_coe, hb, h.ne_top]

@[simp]

中文:
定理 toNNReal_strict_mono
  条件: (hb : b != ∞) (h : a < b)
  结论: a.toNN实数 < b.toNN实数
  证明: by
  simpa [← ENNReal.coe_lt_coe, hb, h.ne_top]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe, coe_lt_coe, h.ne_top, ne_top
-/
theorem toNNReal_strict_mono (hb : b != ∞) (h : a < b) : a.toNNReal < b.toNNReal := by
  simpa [← ENNReal.coe_lt_coe, hb, h.ne_top]

@[simp]
/--
theorem `toNNReal_lt_toNNReal` / 定理 `toNNReal_lt_toNNReal`

English:
theorem toNNReal_lt_toNNReal
  given: (ha : a != ∞) (hb : b != ∞)
  statement: a.toNNReal < b.toNNReal ↔ a < b
  proof: ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_lt_coe], toNNReal_strict_mono hb⟩

中文:
定理 toNNReal_lt_toNNReal
  条件: (ha : a != ∞) (hb : b != ∞)
  结论: a.toNN实数 < b.toNN实数 ↔ a < b
  证明: ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_lt_coe], toNNReal_strict_mono hb⟩

Depends on / 依赖: coe_lt_coe, coe_toNNReal, toNNReal_strict_mono
-/
theorem toNNReal_lt_toNNReal (ha : a != ∞) (hb : b != ∞) : a.toNNReal < b.toNNReal ↔ a < b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_lt_coe], toNNReal_strict_mono hb⟩

/--
theorem `toNNReal_lt_of_lt_coe` / 定理 `toNNReal_lt_of_lt_coe`

English:
theorem toNNReal_lt_of_lt_coe
  given: (h : a < p)
  statement: a.toNNReal < p
  proof: @toNNReal_coe p ▸ toNNReal_strict_mono coe_ne_top h

中文:
定理 toNNReal_lt_of_lt_coe
  条件: (h : a < p)
  结论: a.toNN实数 < p
  证明: @toNNReal_coe p ▸ toNNReal_strict_mono coe_ne_top h

Depends on / 依赖: coe_ne_top, toNNReal_coe, toNNReal_strict_mono
-/
theorem toNNReal_lt_of_lt_coe (h : a < p) : a.toNNReal < p :=
  @toNNReal_coe p ▸ toNNReal_strict_mono coe_ne_top h

/--
theorem `toReal_max` / 定理 `toReal_max`

English:
theorem toReal_max
  given: (hr : a != ∞) (hp : b != ∞)
  proof: (le_total a b).elim
    (fun h => by simp only [h, ENNReal.toReal_mono hp h, max_eq_right]) fun h => by
    simp only [h, ENNReal.toReal_mono hr h, max_eq_left]

中文:
定理 toReal_max
  条件: (hr : a != ∞) (hp : b != ∞)
  证明: (le_total a b).elim
    (fun h => by simp only [h, ENNReal.toReal_mono hp h, max_eq_right]) fun h => by
    simp only [h, ENNReal.toReal_mono hr h, max_eq_left]

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, le_total, max_eq_left, max_eq_right, toReal_mono
-/
theorem toReal_max (hr : a != ∞) (hp : b != ∞) :
    ENNReal.toReal (max a b) = max (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim
    (fun h => by simp only [h, ENNReal.toReal_mono hp h, max_eq_right]) fun h => by
    simp only [h, ENNReal.toReal_mono hr h, max_eq_left]

/--
theorem `toReal_min` / 定理 `toReal_min`

English:
theorem toReal_min
  given: {a b : Real>=0∞} (hr : a != ∞) (hp : b != ∞)
  proof: (le_total a b).elim (fun h => by simp only [h, ENNReal.toReal_mono hp h, min_eq_left])
    fun h => by simp only [h, ENNReal.toReal_mono hr h, min_eq_right]

中文:
定理 toReal_min
  条件: {a b : 实数>=0∞} (hr : a != ∞) (hp : b != ∞)
  证明: (le_total a b).elim (fun h => by simp only [h, ENNReal.toReal_mono hp h, min_eq_left])
    fun h => by simp only [h, ENNReal.toReal_mono hr h, min_eq_right]

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, le_total, min_eq_left, min_eq_right, toReal_mono
-/
theorem toReal_min {a b : Real>=0∞} (hr : a != ∞) (hp : b != ∞) :
    ENNReal.toReal (min a b) = min (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim (fun h => by simp only [h, ENNReal.toReal_mono hp h, min_eq_left])
    fun h => by simp only [h, ENNReal.toReal_mono hr h, min_eq_right]

/--
theorem `toReal_sup` / 定理 `toReal_sup`

English:
theorem toReal_sup
  given: {a b : Real>=0∞}
  statement: a != ∞ -> b != ∞ -> (a ⊔ b).toReal = a.toReal ⊔ b.toReal
  proof: toReal_max

中文:
定理 toReal_sup
  条件: {a b : 实数>=0∞}
  结论: a != ∞ -> b != ∞ -> (a ⊔ b).to实数 = a.to实数 ⊔ b.to实数
  证明: toReal_max

Depends on / 依赖: toReal_max
-/
theorem toReal_sup {a b : Real>=0∞} : a != ∞ -> b != ∞ -> (a ⊔ b).toReal = a.toReal ⊔ b.toReal :=
  toReal_max

/--
theorem `toReal_inf` / 定理 `toReal_inf`

English:
theorem toReal_inf
  given: {a b : Real>=0∞}
  statement: a != ∞ -> b != ∞ -> (a ⊓ b).toReal = a.toReal ⊓ b.toReal
  proof: toReal_min

中文:
定理 toReal_inf
  条件: {a b : 实数>=0∞}
  结论: a != ∞ -> b != ∞ -> (a ⊓ b).to实数 = a.to实数 ⊓ b.to实数
  证明: toReal_min

Depends on / 依赖: toReal_min
-/
theorem toReal_inf {a b : Real>=0∞} : a != ∞ -> b != ∞ -> (a ⊓ b).toReal = a.toReal ⊓ b.toReal :=
  toReal_min

/--
theorem `toNNReal_pos_iff` / 定理 `toNNReal_pos_iff`

English:
theorem toNNReal_pos_iff
  statement: 0 < a.toNNReal ↔ 0 < a ∧ a < ∞
  proof: by
  induction a <;> simp

中文:
定理 toNNReal_pos_iff
  结论: 0 < a.toNN实数 ↔ 0 < a ∧ a < ∞
  证明: by
  induction a <;> simp
-/
theorem toNNReal_pos_iff : 0 < a.toNNReal ↔ 0 < a ∧ a < ∞ := by
  induction a <;> simp

/--
theorem `toNNReal_pos` / 定理 `toNNReal_pos`

English:
theorem toNNReal_pos
  given: {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a != ∞)
  statement: 0 < a.toNNReal
  proof: toNNReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

中文:
定理 toNNReal_pos
  条件: {a : 实数>=0∞} (ha₀ : a != 0) (ha_top : a != ∞)
  结论: 0 < a.toNN实数
  证明: toNNReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

Depends on / 依赖: bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, ha_top, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, toNNReal_pos_iff, toNNReal_pos_iff.mpr
-/
theorem toNNReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a != ∞) : 0 < a.toNNReal :=
  toNNReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

/--
theorem `toReal_pos_iff` / 定理 `toReal_pos_iff`

English:
theorem toReal_pos_iff
  statement: 0 < a.toReal ↔ 0 < a ∧ a < ∞
  proof: NNReal.coe_pos.trans toNNReal_pos_iff

中文:
定理 toReal_pos_iff
  结论: 0 < a.to实数 ↔ 0 < a ∧ a < ∞
  证明: NNReal.coe_pos.trans toNNReal_pos_iff

Depends on / 依赖: NNReal, NNReal.coe_pos.trans, coe_pos, toNNReal_pos_iff
-/
theorem toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞ :=
  NNReal.coe_pos.trans toNNReal_pos_iff

/--
theorem `toReal_pos` / 定理 `toReal_pos`

English:
theorem toReal_pos
  given: {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a != ∞)
  statement: 0 < a.toReal
  proof: toReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

@[gcongr, bound]

中文:
定理 toReal_pos
  条件: {a : 实数>=0∞} (ha₀ : a != 0) (ha_top : a != ∞)
  结论: 0 < a.to实数
  证明: toReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

@[gcongr, bound]

Depends on / 依赖: bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, ha_top, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, toReal_pos_iff, toReal_pos_iff.mpr
-/
theorem toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a != ∞) : 0 < a.toReal :=
  toReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

@[gcongr, bound]
/--
theorem `ofReal_le_ofReal` / 定理 `ofReal_le_ofReal`

English:
theorem ofReal_le_ofReal
  given: {p q : Real} (h : p <= q)
  statement: ENNReal.ofReal p <= ENNReal.ofReal q
  proof: by
  simp [ENNReal.ofReal, Real.toNNReal_le_toNNReal h]

中文:
定理 ofReal_le_ofReal
  条件: {p q : 实数} (h : p <= q)
  结论: ENN实数.of实数 p <= ENN实数.of实数 q
  证明: by
  simp [ENNReal.ofReal, Real.toNNReal_le_toNNReal h]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_le_toNNReal, ofReal, toNNReal_le_toNNReal
-/
theorem ofReal_le_ofReal {p q : Real} (h : p <= q) : ENNReal.ofReal p <= ENNReal.ofReal q := by
  simp [ENNReal.ofReal, Real.toNNReal_le_toNNReal h]

/--
lemma `ofReal_mono` / 引理 `ofReal_mono`

English:
lemma ofReal_mono
  statement: Monotone ENNReal.ofReal
  proof: fun _ _ => ENNReal.ofReal_le_ofReal

中文:
引理 ofReal_mono
  结论: Monotone ENN实数.of实数
  证明: fun _ _ => ENNReal.ofReal_le_ofReal

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, ofReal_le_ofReal
-/
lemma ofReal_mono : Monotone ENNReal.ofReal := fun _ _ => ENNReal.ofReal_le_ofReal

/--
theorem `ofReal_le_of_le_toReal` / 定理 `ofReal_le_of_le_toReal`

English:
theorem ofReal_le_of_le_toReal
  given: {a : Real} {b : Real>=0∞} (h : a <= ENNReal.toReal b)
  proof: (ofReal_le_ofReal h).trans ofReal_toReal_le

@[simp]

中文:
定理 ofReal_le_of_le_toReal
  条件: {a : 实数} {b : 实数>=0∞} (h : a <= ENN实数.to实数 b)
  证明: (ofReal_le_ofReal h).trans ofReal_toReal_le

@[simp]

Depends on / 依赖: ofReal_le_ofReal, ofReal_toReal_le
-/
theorem ofReal_le_of_le_toReal {a : Real} {b : Real>=0∞} (h : a <= ENNReal.toReal b) :
    ENNReal.ofReal a <= b :=
  (ofReal_le_ofReal h).trans ofReal_toReal_le

@[simp]
/--
theorem `ofReal_le_ofReal_iff` / 定理 `ofReal_le_ofReal_iff`

English:
theorem ofReal_le_ofReal_iff
  given: {p q : Real} (h : 0 <= q)
  proof: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_le_coe]; rw [Real.toNNReal_le_toNNReal_iff h]

中文:
定理 ofReal_le_ofReal_iff
  条件: {p q : 实数} (h : 0 <= q)
  证明: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_le_coe]; rw [Real.toNNReal_le_toNNReal_iff h]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_le_toNNReal_iff, coe_le_coe, ofReal, toNNReal_le_toNNReal_iff
-/
theorem ofReal_le_ofReal_iff {p q : Real} (h : 0 <= q) :
    ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q := by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_le_coe]; rw [Real.toNNReal_le_toNNReal_iff h]

/--
lemma `ofReal_le_ofReal_iff'` / 引理 `ofReal_le_ofReal_iff'`

English:
lemma ofReal_le_ofReal_iff'
  given: {p q : Real}
  statement: ENNReal.ofReal p <= .ofReal q ↔ p <= q ∨ p <= 0
  proof: coe_le_coe.trans Real.toNNReal_le_toNNReal_iff'

@[simp, norm_cast]

中文:
引理 ofReal_le_ofReal_iff'
  条件: {p q : 实数}
  结论: ENN实数.of实数 p <= .of实数 q ↔ p <= q ∨ p <= 0
  证明: coe_le_coe.trans Real.toNNReal_le_toNNReal_iff'

@[simp, norm_cast]

Depends on / 依赖: Real.toNNReal_le_toNNReal_iff, coe_le_coe, coe_le_coe.trans, toNNReal_le_toNNReal_iff
-/
lemma ofReal_le_ofReal_iff' {p q : Real} : ENNReal.ofReal p <= .ofReal q ↔ p <= q ∨ p <= 0 :=
  coe_le_coe.trans Real.toNNReal_le_toNNReal_iff'

@[simp, norm_cast]
/--
lemma `ofReal_le_coe` / 引理 `ofReal_le_coe`

English:
lemma ofReal_le_coe
  given: {a : Real} {b : Real>=0}
  statement: ENNReal.ofReal a <= b ↔ a <= b
  proof: by
  simp [← ofReal_le_ofReal_iff]

中文:
引理 ofReal_le_coe
  条件: {a : 实数} {b : 实数>=0}
  结论: ENN实数.of实数 a <= b ↔ a <= b
  证明: by
  simp [← ofReal_le_ofReal_iff]

Depends on / 依赖: ofReal_le_ofReal_iff
-/
lemma ofReal_le_coe {a : Real} {b : Real>=0} : ENNReal.ofReal a <= b ↔ a <= b := by
  simp [← ofReal_le_ofReal_iff]

/--
lemma `ofReal_lt_ofReal_iff'` / 引理 `ofReal_lt_ofReal_iff'`

English:
lemma ofReal_lt_ofReal_iff'
  given: {p q : Real}
  statement: ENNReal.ofReal p < .ofReal q ↔ p < q ∧ 0 < q
  proof: coe_lt_coe.trans Real.toNNReal_lt_toNNReal_iff'

@[simp]

中文:
引理 ofReal_lt_ofReal_iff'
  条件: {p q : 实数}
  结论: ENN实数.of实数 p < .of实数 q ↔ p < q ∧ 0 < q
  证明: coe_lt_coe.trans Real.toNNReal_lt_toNNReal_iff'

@[simp]

Depends on / 依赖: Real.toNNReal_lt_toNNReal_iff, coe_lt_coe, coe_lt_coe.trans, toNNReal_lt_toNNReal_iff
-/
lemma ofReal_lt_ofReal_iff' {p q : Real} : ENNReal.ofReal p < .ofReal q ↔ p < q ∧ 0 < q :=
  coe_lt_coe.trans Real.toNNReal_lt_toNNReal_iff'

@[simp]
/--
theorem `ofReal_eq_ofReal_iff` / 定理 `ofReal_eq_ofReal_iff`

English:
theorem ofReal_eq_ofReal_iff
  given: {p q : Real} (hp : 0 <= p) (hq : 0 <= q)
  proof: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_inj]; rw [Real.toNNReal_eq_toNNReal_iff hp hq]

@[simp]

中文:
定理 ofReal_eq_ofReal_iff
  条件: {p q : 实数} (hp : 0 <= p) (hq : 0 <= q)
  证明: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_inj]; rw [Real.toNNReal_eq_toNNReal_iff hp hq]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_eq_toNNReal_iff, coe_inj, ofReal, toNNReal_eq_toNNReal_iff
-/
theorem ofReal_eq_ofReal_iff {p q : Real} (hp : 0 <= p) (hq : 0 <= q) :
    ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q := by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_inj]; rw [Real.toNNReal_eq_toNNReal_iff hp hq]

@[simp]
/--
theorem `ofReal_lt_ofReal_iff` / 定理 `ofReal_lt_ofReal_iff`

English:
theorem ofReal_lt_ofReal_iff
  given: {p q : Real} (h : 0 < q)
  proof: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_lt_coe]; rw [Real.toNNReal_lt_toNNReal_iff h]

中文:
定理 ofReal_lt_ofReal_iff
  条件: {p q : 实数} (h : 0 < q)
  证明: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_lt_coe]; rw [Real.toNNReal_lt_toNNReal_iff h]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_lt_toNNReal_iff, coe_lt_coe, ofReal, toNNReal_lt_toNNReal_iff
-/
theorem ofReal_lt_ofReal_iff {p q : Real} (h : 0 < q) :
    ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q := by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_lt_coe]; rw [Real.toNNReal_lt_toNNReal_iff h]

/--
theorem `ofReal_lt_ofReal_iff_of_nonneg` / 定理 `ofReal_lt_ofReal_iff_of_nonneg`

English:
theorem ofReal_lt_ofReal_iff_of_nonneg
  given: {p q : Real} (hp : 0 <= p)
  proof: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_lt_coe]; rw [Real.toNNReal_lt_toNNReal_iff_of_nonneg hp]

@[simp]

中文:
定理 ofReal_lt_ofReal_iff_of_nonneg
  条件: {p q : 实数} (hp : 0 <= p)
  证明: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_lt_coe]; rw [Real.toNNReal_lt_toNNReal_iff_of_nonneg hp]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_lt_toNNReal_iff_of_nonneg, coe_lt_coe, ofReal, toNNReal_lt_toNNReal_iff_of_nonneg
-/
theorem ofReal_lt_ofReal_iff_of_nonneg {p q : Real} (hp : 0 <= p) :
    ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q := by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [coe_lt_coe]; rw [Real.toNNReal_lt_toNNReal_iff_of_nonneg hp]

@[simp]
/--
theorem `ofReal_pos` / 定理 `ofReal_pos`

English:
theorem ofReal_pos
  given: {p : Real}
  statement: 0 < ENNReal.ofReal p ↔ 0 < p
  proof: by simp [ENNReal.ofReal]

@[bound] private alias ⟨_, Bound.ofReal_pos_of_pos⟩ := ofReal_pos

@[simp]

中文:
定理 ofReal_pos
  条件: {p : 实数}
  结论: 0 < ENN实数.of实数 p ↔ 0 < p
  证明: by simp [ENNReal.ofReal]

@[bound] private alias ⟨_, Bound.ofReal_pos_of_pos⟩ := ofReal_pos

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, ofReal
-/
theorem ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p := by simp [ENNReal.ofReal]

@[bound] private alias ⟨_, Bound.ofReal_pos_of_pos⟩ := ofReal_pos

@[simp]
/--
theorem `ofReal_eq_zero` / 定理 `ofReal_eq_zero`

English:
theorem ofReal_eq_zero
  given: {p : Real}
  statement: ENNReal.ofReal p = 0 ↔ p <= 0
  proof: by simp [ENNReal.ofReal]

中文:
定理 ofReal_eq_zero
  条件: {p : 实数}
  结论: ENN实数.of实数 p = 0 ↔ p <= 0
  证明: by simp [ENNReal.ofReal]

Depends on / 依赖: ENNReal, ENNReal.ofReal, ofReal
-/
theorem ofReal_eq_zero {p : Real} : ENNReal.ofReal p = 0 ↔ p <= 0 := by simp [ENNReal.ofReal]

/--
lemma `ofReal_min` / 引理 `ofReal_min`

English:
lemma ofReal_min
  given: (x y : Real)
  statement: ENNReal.ofReal (min x y) = min (.ofReal x) (.ofReal y)
  proof: ofReal_mono.map_min

中文:
引理 ofReal_min
  条件: (x y : 实数)
  结论: ENN实数.of实数 (min x y) = min (.of实数 x) (.of实数 y)
  证明: ofReal_mono.map_min
-/
@[simp] lemma ofReal_min (x y : Real) : ENNReal.ofReal (min x y) = min (.ofReal x) (.ofReal y) :=
  ofReal_mono.map_min

/--
lemma `ofReal_max` / 引理 `ofReal_max`

English:
lemma ofReal_max
  given: (x y : Real)
  statement: ENNReal.ofReal (max x y) = max (.ofReal x) (.ofReal y)
  proof: ofReal_mono.map_max

中文:
引理 ofReal_max
  条件: (x y : 实数)
  结论: ENN实数.of实数 (max x y) = max (.of实数 x) (.of实数 y)
  证明: ofReal_mono.map_max
-/
@[simp] lemma ofReal_max (x y : Real) : ENNReal.ofReal (max x y) = max (.ofReal x) (.ofReal y) :=
  ofReal_mono.map_max

/--
theorem `ofReal_ne_zero_iff` / 定理 `ofReal_ne_zero_iff`

English:
theorem ofReal_ne_zero_iff
  given: {r : Real}
  statement: ENNReal.ofReal r != 0 ↔ 0 < r
  proof: by
  rw [← pos_iff_ne_zero]; rw [ENNReal.ofReal_pos]

@[simp]

中文:
定理 ofReal_ne_zero_iff
  条件: {r : 实数}
  结论: ENN实数.of实数 r != 0 ↔ 0 < r
  证明: by
  rw [← pos_iff_ne_zero]; rw [ENNReal.ofReal_pos]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_pos, ofReal_pos, pos_iff_ne_zero
-/
theorem ofReal_ne_zero_iff {r : Real} : ENNReal.ofReal r != 0 ↔ 0 < r := by
  rw [← pos_iff_ne_zero]; rw [ENNReal.ofReal_pos]

@[simp]
/--
theorem `zero_eq_ofReal` / 定理 `zero_eq_ofReal`

English:
theorem zero_eq_ofReal
  given: {p : Real}
  statement: 0 = ENNReal.ofReal p ↔ p <= 0
  proof: eq_comm.trans ofReal_eq_zero

alias ⟨_, ofReal_of_nonpos⟩ := ofReal_eq_zero

@[simp]

中文:
定理 zero_eq_ofReal
  条件: {p : 实数}
  结论: 0 = ENN实数.of实数 p ↔ p <= 0
  证明: eq_comm.trans ofReal_eq_zero

alias ⟨_, ofReal_of_nonpos⟩ := ofReal_eq_zero

@[simp]

Depends on / 依赖: MonoidHom, MonoidHom.mk, RingEquiv, RingEquiv.injective, compRingEquiv, comp_one, eq_comm, eq_comm.trans, injective, map_mul, ofReal_eq_zero, of_injective
-/
theorem zero_eq_ofReal {p : Real} : 0 = ENNReal.ofReal p ↔ p <= 0 :=
  eq_comm.trans ofReal_eq_zero

alias ⟨_, ofReal_of_nonpos⟩ := ofReal_eq_zero

@[simp]
/--
lemma `ofReal_lt_natCast` / 引理 `ofReal_lt_natCast`

English:
lemma ofReal_lt_natCast
  given: {p : Real} {n : Nat} (hn : n != 0)
  statement: ENNReal.ofReal p < n ↔ p < n
  proof: by
  exact mod_cast ofReal_lt_ofReal_iff (Nat.cast_pos.2 hn.bot_lt)

@[simp]

中文:
引理 ofReal_lt_natCast
  条件: {p : 实数} {n : 自然数} (hn : n != 0)
  结论: ENN实数.of实数 p < n ↔ p < n
  证明: by
  exact mod_cast ofReal_lt_ofReal_iff (Nat.cast_pos.2 hn.bot_lt)

@[simp]

Depends on / 依赖: Nat.cast_pos, bot_lt, cast_pos, hn.bot_lt, mod_cast, ofReal_lt_ofReal_iff
-/
lemma ofReal_lt_natCast {p : Real} {n : Nat} (hn : n != 0) : ENNReal.ofReal p < n ↔ p < n := by
  exact mod_cast ofReal_lt_ofReal_iff (Nat.cast_pos.2 hn.bot_lt)

@[simp]
/--
lemma `ofReal_lt_one` / 引理 `ofReal_lt_one`

English:
lemma ofReal_lt_one
  given: {p : Real}
  statement: ENNReal.ofReal p < 1 ↔ p < 1
  proof: by
  exact mod_cast ofReal_lt_natCast one_ne_zero

@[simp]

中文:
引理 ofReal_lt_one
  条件: {p : 实数}
  结论: ENN实数.of实数 p < 1 ↔ p < 1
  证明: by
  exact mod_cast ofReal_lt_natCast one_ne_zero

@[simp]

Depends on / 依赖: mod_cast, ofReal_lt_natCast, one_ne_zero
-/
lemma ofReal_lt_one {p : Real} : ENNReal.ofReal p < 1 ↔ p < 1 := by
  exact mod_cast ofReal_lt_natCast one_ne_zero

@[simp]
/--
lemma `ofReal_lt_ofNat` / 引理 `ofReal_lt_ofNat`

English:
lemma ofReal_lt_ofNat
  given: {p : Real} {n : Nat} [n.AtLeastTwo]
  proof: ofReal_lt_natCast (NeZero.ne n)

@[simp]

中文:
引理 ofReal_lt_ofNat
  条件: {p : 实数} {n : 自然数} [n.AtLeastTwo]
  证明: ofReal_lt_natCast (NeZero.ne n)

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, ofReal_lt_natCast
-/
lemma ofReal_lt_ofNat {p : Real} {n : Nat} [n.AtLeastTwo] :
    ENNReal.ofReal p < ofNat(n) ↔ p < OfNat.ofNat n :=
  ofReal_lt_natCast (NeZero.ne n)

@[simp]
/--
lemma `natCast_le_ofReal` / 引理 `natCast_le_ofReal`

English:
lemma natCast_le_ofReal
  given: {n : Nat} {p : Real} (hn : n != 0)
  statement: n <= ENNReal.ofReal p ↔ n <= p
  proof: by
  simp only [← not_lt, ofReal_lt_natCast hn]

@[simp]

中文:
引理 natCast_le_ofReal
  条件: {n : 自然数} {p : 实数} (hn : n != 0)
  结论: n <= ENN实数.of实数 p ↔ n <= p
  证明: by
  simp only [← not_lt, ofReal_lt_natCast hn]

@[simp]

Depends on / 依赖: not_lt, ofReal_lt_natCast
-/
lemma natCast_le_ofReal {n : Nat} {p : Real} (hn : n != 0) : n <= ENNReal.ofReal p ↔ n <= p := by
  simp only [← not_lt, ofReal_lt_natCast hn]

@[simp]
/--
lemma `one_le_ofReal` / 引理 `one_le_ofReal`

English:
lemma one_le_ofReal
  given: {p : Real}
  statement: 1 <= ENNReal.ofReal p ↔ 1 <= p
  proof: by
  exact mod_cast natCast_le_ofReal one_ne_zero

@[simp]

中文:
引理 one_le_ofReal
  条件: {p : 实数}
  结论: 1 <= ENN实数.of实数 p ↔ 1 <= p
  证明: by
  exact mod_cast natCast_le_ofReal one_ne_zero

@[simp]

Depends on / 依赖: mod_cast, natCast_le_ofReal, one_ne_zero
-/
lemma one_le_ofReal {p : Real} : 1 <= ENNReal.ofReal p ↔ 1 <= p := by
  exact mod_cast natCast_le_ofReal one_ne_zero

@[simp]
/--
lemma `ofNat_le_ofReal` / 引理 `ofNat_le_ofReal`

English:
lemma ofNat_le_ofReal
  given: {n : Nat} [n.AtLeastTwo] {p : Real}
  proof: natCast_le_ofReal (NeZero.ne n)

@[simp, norm_cast]

中文:
引理 ofNat_le_ofReal
  条件: {n : 自然数} [n.AtLeastTwo] {p : 实数}
  证明: natCast_le_ofReal (NeZero.ne n)

@[simp, norm_cast]

Depends on / 依赖: NeZero, NeZero.ne, natCast_le_ofReal
-/
lemma ofNat_le_ofReal {n : Nat} [n.AtLeastTwo] {p : Real} :
    ofNat(n) <= ENNReal.ofReal p ↔ OfNat.ofNat n <= p :=
  natCast_le_ofReal (NeZero.ne n)

@[simp, norm_cast]
/--
lemma `ofReal_le_natCast` / 引理 `ofReal_le_natCast`

English:
lemma ofReal_le_natCast
  given: {r : Real} {n : Nat}
  statement: ENNReal.ofReal r <= n ↔ r <= n
  proof: coe_le_coe.trans Real.toNNReal_le_natCast

@[simp]

中文:
引理 ofReal_le_natCast
  条件: {r : 实数} {n : 自然数}
  结论: ENN实数.of实数 r <= n ↔ r <= n
  证明: coe_le_coe.trans Real.toNNReal_le_natCast

@[simp]

Depends on / 依赖: Real.toNNReal_le_natCast, coe_le_coe, coe_le_coe.trans, toNNReal_le_natCast
-/
lemma ofReal_le_natCast {r : Real} {n : Nat} : ENNReal.ofReal r <= n ↔ r <= n :=
  coe_le_coe.trans Real.toNNReal_le_natCast

@[simp]
/--
lemma `ofReal_le_one` / 引理 `ofReal_le_one`

English:
lemma ofReal_le_one
  given: {r : Real}
  statement: ENNReal.ofReal r <= 1 ↔ r <= 1
  proof: coe_le_coe.trans Real.toNNReal_le_one

@[simp]

中文:
引理 ofReal_le_one
  条件: {r : 实数}
  结论: ENN实数.of实数 r <= 1 ↔ r <= 1
  证明: coe_le_coe.trans Real.toNNReal_le_one

@[simp]

Depends on / 依赖: Real.toNNReal_le_one, coe_le_coe, coe_le_coe.trans, toNNReal_le_one
-/
lemma ofReal_le_one {r : Real} : ENNReal.ofReal r <= 1 ↔ r <= 1 :=
  coe_le_coe.trans Real.toNNReal_le_one

@[simp]
/--
lemma `ofReal_le_ofNat` / 引理 `ofReal_le_ofNat`

English:
lemma ofReal_le_ofNat
  given: {r : Real} {n : Nat} [n.AtLeastTwo]
  proof: ofReal_le_natCast

@[simp]

中文:
引理 ofReal_le_ofNat
  条件: {r : 实数} {n : 自然数} [n.AtLeastTwo]
  证明: ofReal_le_natCast

@[simp]

Depends on / 依赖: ofReal_le_natCast
-/
lemma ofReal_le_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] :
    ENNReal.ofReal r <= ofNat(n) ↔ r <= OfNat.ofNat n :=
  ofReal_le_natCast

@[simp]
/--
lemma `natCast_lt_ofReal` / 引理 `natCast_lt_ofReal`

English:
lemma natCast_lt_ofReal
  given: {n : Nat} {r : Real}
  statement: n < ENNReal.ofReal r ↔ n < r
  proof: coe_lt_coe.trans Real.natCast_lt_toNNReal

@[simp]

中文:
引理 natCast_lt_ofReal
  条件: {n : 自然数} {r : 实数}
  结论: n < ENN实数.of实数 r ↔ n < r
  证明: coe_lt_coe.trans Real.natCast_lt_toNNReal

@[simp]

Depends on / 依赖: Real.natCast_lt_toNNReal, coe_lt_coe, coe_lt_coe.trans, natCast_lt_toNNReal
-/
lemma natCast_lt_ofReal {n : Nat} {r : Real} : n < ENNReal.ofReal r ↔ n < r :=
  coe_lt_coe.trans Real.natCast_lt_toNNReal

@[simp]
/--
lemma `one_lt_ofReal` / 引理 `one_lt_ofReal`

English:
lemma one_lt_ofReal
  given: {r : Real}
  statement: 1 < ENNReal.ofReal r ↔ 1 < r
  proof: coe_lt_coe.trans Real.one_lt_toNNReal

@[simp]

中文:
引理 one_lt_ofReal
  条件: {r : 实数}
  结论: 1 < ENN实数.of实数 r ↔ 1 < r
  证明: coe_lt_coe.trans Real.one_lt_toNNReal

@[simp]

Depends on / 依赖: Real.one_lt_toNNReal, coe_lt_coe, coe_lt_coe.trans, one_lt_toNNReal
-/
lemma one_lt_ofReal {r : Real} : 1 < ENNReal.ofReal r ↔ 1 < r := coe_lt_coe.trans Real.one_lt_toNNReal

@[simp]
/--
lemma `ofNat_lt_ofReal` / 引理 `ofNat_lt_ofReal`

English:
lemma ofNat_lt_ofReal
  given: {n : Nat} [n.AtLeastTwo] {r : Real}
  proof: natCast_lt_ofReal

@[simp]

中文:
引理 ofNat_lt_ofReal
  条件: {n : 自然数} [n.AtLeastTwo] {r : 实数}
  证明: natCast_lt_ofReal

@[simp]

Depends on / 依赖: natCast_lt_ofReal
-/
lemma ofNat_lt_ofReal {n : Nat} [n.AtLeastTwo] {r : Real} :
    ofNat(n) < ENNReal.ofReal r ↔ OfNat.ofNat n < r :=
  natCast_lt_ofReal

@[simp]
/--
lemma `ofReal_eq_natCast` / 引理 `ofReal_eq_natCast`

English:
lemma ofReal_eq_natCast
  given: {r : Real} {n : Nat} (h : n != 0)
  statement: ENNReal.ofReal r = n ↔ r = n
  proof: ENNReal.coe_inj.trans Real.toNNReal_eq_natCast h

@[simp]

中文:
引理 ofReal_eq_natCast
  条件: {r : 实数} {n : 自然数} (h : n != 0)
  结论: ENN实数.of实数 r = n ↔ r = n
  证明: ENNReal.coe_inj.trans Real.toNNReal_eq_natCast h

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_inj.trans, Real.toNNReal_eq_natCast, coe_inj, toNNReal_eq_natCast
-/
lemma ofReal_eq_natCast {r : Real} {n : Nat} (h : n != 0) : ENNReal.ofReal r = n ↔ r = n :=
ENNReal.coe_inj.trans Real.toNNReal_eq_natCast h

@[simp]
/--
lemma `ofReal_eq_one` / 引理 `ofReal_eq_one`

English:
lemma ofReal_eq_one
  given: {r : Real}
  statement: ENNReal.ofReal r = 1 ↔ r = 1
  proof: ENNReal.coe_inj.trans Real.toNNReal_eq_one

@[simp]

中文:
引理 ofReal_eq_one
  条件: {r : 实数}
  结论: ENN实数.of实数 r = 1 ↔ r = 1
  证明: ENNReal.coe_inj.trans Real.toNNReal_eq_one

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_inj.trans, Real.toNNReal_eq_one, coe_inj, toNNReal_eq_one
-/
lemma ofReal_eq_one {r : Real} : ENNReal.ofReal r = 1 ↔ r = 1 :=
  ENNReal.coe_inj.trans Real.toNNReal_eq_one

@[simp]
/--
lemma `ofReal_eq_ofNat` / 引理 `ofReal_eq_ofNat`

English:
lemma ofReal_eq_ofNat
  given: {r : Real} {n : Nat} [n.AtLeastTwo]
  proof: ofReal_eq_natCast (NeZero.ne n)

中文:
引理 ofReal_eq_ofNat
  条件: {r : 实数} {n : 自然数} [n.AtLeastTwo]
  证明: ofReal_eq_natCast (NeZero.ne n)

Depends on / 依赖: NeZero, NeZero.ne, ofReal_eq_natCast
-/
lemma ofReal_eq_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] :
    ENNReal.ofReal r = ofNat(n) ↔ r = OfNat.ofNat n :=
  ofReal_eq_natCast (NeZero.ne n)

/--
theorem `ofReal_le_iff_le_toReal` / 定理 `ofReal_le_iff_le_toReal`

English:
theorem ofReal_le_iff_le_toReal
  given: {a : Real} {b : Real>=0∞} (hb : b != ∞)
  proof: by
  lift b to Real>=0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_le_iff_le_coe

中文:
定理 ofReal_le_iff_le_toReal
  条件: {a : 实数} {b : 实数>=0∞} (hb : b != ∞)
  证明: by
  lift b to Real>=0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_le_iff_le_coe

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal, Real.toNNReal_le_iff_le_coe, ofReal, toNNReal_le_iff_le_coe, toReal
-/
theorem ofReal_le_iff_le_toReal {a : Real} {b : Real>=0∞} (hb : b != ∞) :
    ENNReal.ofReal a <= b ↔ a <= ENNReal.toReal b := by
  lift b to Real>=0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_le_iff_le_coe

/--
theorem `ofReal_lt_iff_lt_toReal` / 定理 `ofReal_lt_iff_lt_toReal`

English:
theorem ofReal_lt_iff_lt_toReal
  given: {a : Real} {b : Real>=0∞} (ha : 0 <= a) (hb : b != ∞)
  proof: by
  lift b to Real>=0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_lt_iff_lt_coe ha

中文:
定理 ofReal_lt_iff_lt_toReal
  条件: {a : 实数} {b : 实数>=0∞} (ha : 0 <= a) (hb : b != ∞)
  证明: by
  lift b to Real>=0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_lt_iff_lt_coe ha

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal, Real.toNNReal_lt_iff_lt_coe, ofReal, toNNReal_lt_iff_lt_coe, toReal
-/
theorem ofReal_lt_iff_lt_toReal {a : Real} {b : Real>=0∞} (ha : 0 <= a) (hb : b != ∞) :
    ENNReal.ofReal a < b ↔ a < ENNReal.toReal b := by
  lift b to Real>=0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_lt_iff_lt_coe ha

/--
lemma `coe_lt_ofReal` / 引理 `coe_lt_ofReal`

English:
lemma coe_lt_ofReal
  given: {a : Real>=0} {b : Real}
  statement: a < ENNReal.ofReal b ↔ a < b
  proof: by
  simp [ENNReal.ofReal, Real.lt_toNNReal_iff_coe_lt]

中文:
引理 coe_lt_ofReal
  条件: {a : 实数>=0} {b : 实数}
  结论: a < ENN实数.of实数 b ↔ a < b
  证明: by
  simp [ENNReal.ofReal, Real.lt_toNNReal_iff_coe_lt]
-/
@[simp] lemma coe_lt_ofReal {a : Real>=0} {b : Real} : a < ENNReal.ofReal b ↔ a < b := by
  simp [ENNReal.ofReal, Real.lt_toNNReal_iff_coe_lt]

/--
theorem `ofReal_lt_coe_iff` / 定理 `ofReal_lt_coe_iff`

English:
theorem ofReal_lt_coe_iff
  given: {a : Real} {b : Real>=0} (ha : 0 <= a)
  statement: ENNReal.ofReal a < b ↔ a < b
  proof: (ofReal_lt_iff_lt_toReal ha coe_ne_top).trans by rw [coe_toReal]

中文:
定理 ofReal_lt_coe_iff
  条件: {a : 实数} {b : 实数>=0} (ha : 0 <= a)
  结论: ENN实数.of实数 a < b ↔ a < b
  证明: (ofReal_lt_iff_lt_toReal ha coe_ne_top).trans by rw [coe_toReal]

Depends on / 依赖: coe_ne_top, coe_toReal, ofReal_lt_iff_lt_toReal
-/
theorem ofReal_lt_coe_iff {a : Real} {b : Real>=0} (ha : 0 <= a) : ENNReal.ofReal a < b ↔ a < b :=
(ofReal_lt_iff_lt_toReal ha coe_ne_top).trans by rw [coe_toReal]

/--
theorem `le_ofReal_iff_toReal_le` / 定理 `le_ofReal_iff_toReal_le`

English:
theorem le_ofReal_iff_toReal_le
  given: {a : Real>=0∞} {b : Real} (ha : a != ∞) (hb : 0 <= b)
  proof: by
  lift a to Real>=0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.le_toNNReal_iff_coe_le hb

中文:
定理 le_ofReal_iff_toReal_le
  条件: {a : 实数>=0∞} {b : 实数} (ha : a != ∞) (hb : 0 <= b)
  证明: by
  lift a to Real>=0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.le_toNNReal_iff_coe_le hb

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal, Real.le_toNNReal_iff_coe_le, le_toNNReal_iff_coe_le, ofReal, toReal
-/
theorem le_ofReal_iff_toReal_le {a : Real>=0∞} {b : Real} (ha : a != ∞) (hb : 0 <= b) :
    a <= ENNReal.ofReal b ↔ ENNReal.toReal a <= b := by
  lift a to Real>=0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.le_toNNReal_iff_coe_le hb

/--
theorem `toReal_le_of_le_ofReal` / 定理 `toReal_le_of_le_ofReal`

English:
theorem toReal_le_of_le_ofReal
  given: {a : Real>=0∞} {b : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b)
  proof: have ha : a != ∞ := ne_top_of_le_ne_top ofReal_ne_top h
  (le_ofReal_iff_toReal_le ha hb).1 h

中文:
定理 toReal_le_of_le_ofReal
  条件: {a : 实数>=0∞} {b : 实数} (hb : 0 <= b) (h : a <= ENN实数.of实数 b)
  证明: have ha : a != ∞ := ne_top_of_le_ne_top ofReal_ne_top h
  (le_ofReal_iff_toReal_le ha hb).1 h

Depends on / 依赖: le_ofReal_iff_toReal_le, ne_top_of_le_ne_top, ofReal_ne_top
-/
theorem toReal_le_of_le_ofReal {a : Real>=0∞} {b : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) :
    ENNReal.toReal a <= b :=
  have ha : a != ∞ := ne_top_of_le_ne_top ofReal_ne_top h
  (le_ofReal_iff_toReal_le ha hb).1 h

/--
theorem `lt_ofReal_iff_toReal_lt` / 定理 `lt_ofReal_iff_toReal_lt`

English:
theorem lt_ofReal_iff_toReal_lt
  given: {a : Real>=0∞} {b : Real} (ha : a != ∞)
  proof: by
  lift a to Real>=0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.lt_toNNReal_iff_coe_lt

中文:
定理 lt_ofReal_iff_toReal_lt
  条件: {a : 实数>=0∞} {b : 实数} (ha : a != ∞)
  证明: by
  lift a to Real>=0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.lt_toNNReal_iff_coe_lt

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal, Real.lt_toNNReal_iff_coe_lt, lt_toNNReal_iff_coe_lt, ofReal, toReal
-/
theorem lt_ofReal_iff_toReal_lt {a : Real>=0∞} {b : Real} (ha : a != ∞) :
    a < ENNReal.ofReal b ↔ ENNReal.toReal a < b := by
  lift a to Real>=0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.lt_toNNReal_iff_coe_lt

/--
theorem `toReal_lt_of_lt_ofReal` / 定理 `toReal_lt_of_lt_ofReal`

English:
theorem toReal_lt_of_lt_ofReal
  given: {b : Real} (h : a < ENNReal.ofReal b)
  statement: ENNReal.toReal a < b
  proof: (lt_ofReal_iff_toReal_lt h.ne_top).1 h

@[simp]

中文:
定理 toReal_lt_of_lt_ofReal
  条件: {b : 实数} (h : a < ENN实数.of实数 b)
  结论: ENN实数.to实数 a < b
  证明: (lt_ofReal_iff_toReal_lt h.ne_top).1 h

@[simp]

Depends on / 依赖: h.ne_top, lt_ofReal_iff_toReal_lt, ne_top
-/
theorem toReal_lt_of_lt_ofReal {b : Real} (h : a < ENNReal.ofReal b) : ENNReal.toReal a < b :=
  (lt_ofReal_iff_toReal_lt h.ne_top).1 h

@[simp]
/--
theorem `ofReal_mul` / 定理 `ofReal_mul`

English:
theorem ofReal_mul
  given: {p q : Real} (hp : 0 <= p)
  proof: by
  simp only [ENNReal.ofReal, ← coe_mul, Real.toNNReal_mul hp]

中文:
定理 ofReal_mul
  条件: {p q : 实数} (hp : 0 <= p)
  证明: by
  simp only [ENNReal.ofReal, ← coe_mul, Real.toNNReal_mul hp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_mul, coe_mul, ofReal, toNNReal_mul
-/
theorem ofReal_mul {p q : Real} (hp : 0 <= p) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  simp only [ENNReal.ofReal, ← coe_mul, Real.toNNReal_mul hp]

/--
theorem `ofReal_mul'` / 定理 `ofReal_mul'`

English:
theorem ofReal_mul'
  given: {p q : Real} (hq : 0 <= q)
  proof: by
  rw [mul_comm]; rw [ofReal_mul hq]; rw [mul_comm]

@[simp]

中文:
定理 ofReal_mul'
  条件: {p q : 实数} (hq : 0 <= q)
  证明: by
  rw [mul_comm]; rw [ofReal_mul hq]; rw [mul_comm]

@[simp]

Depends on / 依赖: mul_comm, ofReal_mul
-/
theorem ofReal_mul' {p q : Real} (hq : 0 <= q) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  rw [mul_comm]; rw [ofReal_mul hq]; rw [mul_comm]

@[simp]
/--
theorem `ofReal_pow` / 定理 `ofReal_pow`

English:
theorem ofReal_pow
  given: {p : Real} (hp : 0 <= p) (n : Nat)
  proof: by
  rw [ofReal_eq_coe_nnreal hp]; rw [← coe_pow]; rw [← ofReal_coe_nnreal]; rw [NNReal.coe_pow]; rw [NNReal.coe_mk]

中文:
定理 ofReal_pow
  条件: {p : 实数} (hp : 0 <= p) (n : 自然数)
  证明: by
  rw [ofReal_eq_coe_nnreal hp]; rw [← coe_pow]; rw [← ofReal_coe_nnreal]; rw [NNReal.coe_pow]; rw [NNReal.coe_mk]

Depends on / 依赖: NNReal, NNReal.coe_mk, NNReal.coe_pow, coe_mk, coe_pow, ofReal_coe_nnreal, ofReal_eq_coe_nnreal
-/
theorem ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) :
    ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n := by
  rw [ofReal_eq_coe_nnreal hp]; rw [← coe_pow]; rw [← ofReal_coe_nnreal]; rw [NNReal.coe_pow]; rw [NNReal.coe_mk]

/--
theorem `ofReal_nsmul` / 定理 `ofReal_nsmul`

English:
theorem ofReal_nsmul
  given: {x : Real} {n : Nat}
  statement: ENNReal.ofReal (n • x) = n • ENNReal.ofReal x
  proof: by
  simp only [nsmul_eq_mul, ← ofReal_natCast n, ← ofReal_mul n.cast_nonneg]

@[simp]

中文:
定理 ofReal_nsmul
  条件: {x : 实数} {n : 自然数}
  结论: ENN实数.of实数 (n • x) = n • ENN实数.of实数 x
  证明: by
  simp only [nsmul_eq_mul, ← ofReal_natCast n, ← ofReal_mul n.cast_nonneg]

@[simp]

Depends on / 依赖: cast_nonneg, n.cast_nonneg, nsmul_eq_mul, ofReal_mul, ofReal_natCast
-/
theorem ofReal_nsmul {x : Real} {n : Nat} : ENNReal.ofReal (n • x) = n • ENNReal.ofReal x := by
  simp only [nsmul_eq_mul, ← ofReal_natCast n, ← ofReal_mul n.cast_nonneg]

@[simp]
/--
theorem `toNNReal_mul` / 定理 `toNNReal_mul`

English:
theorem toNNReal_mul
  given: {a b : Real>=0∞}
  statement: (a * b).toNNReal = a.toNNReal * b.toNNReal
  proof: WithTop.untopD_zero_mul a b

中文:
定理 toNNReal_mul
  条件: {a b : 实数>=0∞}
  结论: (a * b).toNN实数 = a.toNN实数 * b.toNN实数
  证明: WithTop.untopD_zero_mul a b

Depends on / 依赖: WithTop, WithTop.untopD_zero_mul, untopD_zero_mul
-/
theorem toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal = a.toNNReal * b.toNNReal :=
  WithTop.untopD_zero_mul a b

/--
theorem `toNNReal_mul_top` / 定理 `toNNReal_mul_top`

English:
theorem toNNReal_mul_top
  given: (a : Real>=0∞)
  statement: ENNReal.toNNReal (a * ∞) = 0
  proof: by simp

中文:
定理 toNNReal_mul_top
  条件: (a : 实数>=0∞)
  结论: ENN实数.toNN实数 (a * ∞) = 0
  证明: by simp
-/
theorem toNNReal_mul_top (a : Real>=0∞) : ENNReal.toNNReal (a * ∞) = 0 := by simp

/--
theorem `toNNReal_top_mul` / 定理 `toNNReal_top_mul`

English:
theorem toNNReal_top_mul
  given: (a : Real>=0∞)
  statement: ENNReal.toNNReal (∞ * a) = 0
  proof: by simp

中文:
定理 toNNReal_top_mul
  条件: (a : 实数>=0∞)
  结论: ENN实数.toNN实数 (∞ * a) = 0
  证明: by simp
-/
theorem toNNReal_top_mul (a : Real>=0∞) : ENNReal.toNNReal (∞ * a) = 0 := by simp

/--
Definition of `toNNRealHom` / `toNNRealHom` 的定义

English:
definition toNNRealHom
  signature: : Real>=0∞ ->*₀ Real>=0 where
  body: ENNReal.toNNReal
  map_one' := toNNReal_coe _
  map_mul' _ _ := toNNReal_mul
  map_zero' := toNNReal_zero

@[simp]

中文:
定义 toNNRealHom
  签名: : 实数>=0∞ ->*₀ 实数>=0 where
  定义体: ENNReal.toNNReal
  map_one' := toNNReal_coe _
  map_mul' _ _ := toNNReal_mul
  map_zero' := toNNReal_zero

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toNNReal, toNNReal
-/
noncomputable def toNNRealHom : Real>=0∞ ->*₀ Real>=0 where
  toFun := ENNReal.toNNReal
  map_one' := toNNReal_coe _
  map_mul' _ _ := toNNReal_mul
  map_zero' := toNNReal_zero

@[simp]
/--
theorem `toNNReal_pow` / 定理 `toNNReal_pow`

English:
theorem toNNReal_pow
  given: (a : Real>=0∞) (n : Nat)
  statement: (a ^ n).toNNReal = a.toNNReal ^ n
  proof: toNNRealHom.map_pow a n

中文:
定理 toNNReal_pow
  条件: (a : 实数>=0∞) (n : 自然数)
  结论: (a ^ n).toNN实数 = a.toNN实数 ^ n
  证明: toNNRealHom.map_pow a n

Depends on / 依赖: map_pow, toNNRealHom, toNNRealHom.map_pow
-/
theorem toNNReal_pow (a : Real>=0∞) (n : Nat) : (a ^ n).toNNReal = a.toNNReal ^ n :=
  toNNRealHom.map_pow a n

/--
Definition of `toRealHom` / `toRealHom` 的定义

English:
definition toRealHom
  signature: : Real>=0∞ ->*₀ Real
  body: (.ofClass NNReal.toRealHom : Real>=0 ->*₀ Real).comp toNNRealHom

@[simp]

中文:
定义 toRealHom
  签名: : 实数>=0∞ ->*₀ 实数
  定义体: (.ofClass NNReal.toRealHom : Real>=0 ->*₀ Real).comp toNNRealHom

@[simp]

Depends on / 依赖: NNReal, NNReal.toRealHom, ofClass, toNNRealHom, toRealHom
-/
noncomputable def toRealHom : Real>=0∞ ->*₀ Real :=
  (.ofClass NNReal.toRealHom : Real>=0 ->*₀ Real).comp toNNRealHom

@[simp]
/--
theorem `toReal_mul` / 定理 `toReal_mul`

English:
theorem toReal_mul
  statement: (a * b).toReal = a.toReal * b.toReal
  proof: toRealHom.map_mul a b

中文:
定理 toReal_mul
  结论: (a * b).to实数 = a.to实数 * b.to实数
  证明: toRealHom.map_mul a b

Depends on / 依赖: map_mul, toRealHom, toRealHom.map_mul
-/
theorem toReal_mul : (a * b).toReal = a.toReal * b.toReal :=
  toRealHom.map_mul a b

/--
theorem `toReal_nsmul` / 定理 `toReal_nsmul`

English:
theorem toReal_nsmul
  given: (a : Real>=0∞) (n : Nat)
  statement: (n • a).toReal = n • a.toReal
  proof: by simp

@[simp]

中文:
定理 toReal_nsmul
  条件: (a : 实数>=0∞) (n : 自然数)
  结论: (n • a).to实数 = n • a.to实数
  证明: by simp

@[simp]
-/
theorem toReal_nsmul (a : Real>=0∞) (n : Nat) : (n • a).toReal = n • a.toReal := by simp

@[simp]
/--
theorem `toReal_pow` / 定理 `toReal_pow`

English:
theorem toReal_pow
  given: (a : Real>=0∞) (n : Nat)
  statement: (a ^ n).toReal = a.toReal ^ n
  proof: toRealHom.map_pow a n

中文:
定理 toReal_pow
  条件: (a : 实数>=0∞) (n : 自然数)
  结论: (a ^ n).to实数 = a.to实数 ^ n
  证明: toRealHom.map_pow a n

Depends on / 依赖: map_pow, toRealHom, toRealHom.map_pow
-/
theorem toReal_pow (a : Real>=0∞) (n : Nat) : (a ^ n).toReal = a.toReal ^ n :=
  toRealHom.map_pow a n

/--
theorem `toReal_ofReal_mul` / 定理 `toReal_ofReal_mul`

English:
theorem toReal_ofReal_mul
  given: (c : Real) (a : Real>=0∞) (h : 0 <= c)
  proof: by
  rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_ofReal h]

中文:
定理 toReal_ofReal_mul
  条件: (c : 实数) (a : 实数>=0∞) (h : 0 <= c)
  证明: by
  rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_ofReal h]

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal, toReal_mul, toReal_ofReal
-/
theorem toReal_ofReal_mul (c : Real) (a : Real>=0∞) (h : 0 <= c) :
    ENNReal.toReal (ENNReal.ofReal c * a) = c * ENNReal.toReal a := by
  rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_ofReal h]

/--
theorem `toReal_mul_top` / 定理 `toReal_mul_top`

English:
theorem toReal_mul_top
  given: (a : Real>=0∞)
  statement: ENNReal.toReal (a * ∞) = 0
  proof: by
  rw [toReal_mul]; rw [toReal_top]; rw [mul_zero]

中文:
定理 toReal_mul_top
  条件: (a : 实数>=0∞)
  结论: ENN实数.to实数 (a * ∞) = 0
  证明: by
  rw [toReal_mul]; rw [toReal_top]; rw [mul_zero]

Depends on / 依赖: mul_zero, toReal_mul, toReal_top
-/
theorem toReal_mul_top (a : Real>=0∞) : ENNReal.toReal (a * ∞) = 0 := by
  rw [toReal_mul]; rw [toReal_top]; rw [mul_zero]

/--
theorem `toReal_top_mul` / 定理 `toReal_top_mul`

English:
theorem toReal_top_mul
  given: (a : Real>=0∞)
  statement: ENNReal.toReal (∞ * a) = 0
  proof: by
  rw [mul_comm]
  exact toReal_mul_top _

中文:
定理 toReal_top_mul
  条件: (a : 实数>=0∞)
  结论: ENN实数.to实数 (∞ * a) = 0
  证明: by
  rw [mul_comm]
  exact toReal_mul_top _

Depends on / 依赖: mul_comm, toReal_mul_top
-/
theorem toReal_top_mul (a : Real>=0∞) : ENNReal.toReal (∞ * a) = 0 := by
  rw [mul_comm]
  exact toReal_mul_top _

/--
theorem `trichotomy` / 定理 `trichotomy`

English:
theorem trichotomy
  given: (p : Real>=0∞)
  statement: p = 0 ∨ p = ∞ ∨ 0 < p.toReal
  proof: by
  simpa only [or_iff_not_imp_left] using toReal_pos

中文:
定理 trichotomy
  条件: (p : 实数>=0∞)
  结论: p = 0 ∨ p = ∞ ∨ 0 < p.to实数
  证明: by
  simpa only [or_iff_not_imp_left] using toReal_pos
-/
protected theorem trichotomy (p : Real>=0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal := by
  simpa only [or_iff_not_imp_left] using toReal_pos

/--
theorem `trichotomy₂` / 定理 `trichotomy₂`

English:
theorem trichotomy₂
  given: {p q : Real>=0∞} (hpq : p <= q)
  proof: by
  rcases eq_or_lt_of_le (bot_le : 0 <= p) with ((rfl : 0 = p) | (hp : 0 < p))
  · simpa using q.trichotomy
  rcases eq_or_lt_of_le (le_top : q <= ∞) with (rfl | hq)
  · simpa using p.trichotomy
  have hq' : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq
  simp [ENNReal

中文:
定理 trichotomy₂
  条件: {p q : 实数>=0∞} (hpq : p <= q)
  证明: by
  rcases eq_or_lt_of_le (bot_le : 0 <= p) with ((rfl : 0 = p) | (hp : 0 < p))
  · simpa using q.trichotomy
  rcases eq_or_lt_of_le (le_top : q <= ∞) with (rfl | hq)
  · simpa using p.trichotomy
  have hq' : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq
  simp [ENNReal
-/
protected theorem trichotomy₂ {p q : Real>=0∞} (hpq : p <= q) :
    p = 0 ∧ q = 0 ∨
      p = 0 ∧ q = ∞ ∨
        p = 0 ∧ 0 < q.toReal ∨
          p = ∞ ∧ q = ∞ ∨
            0 < p.toReal ∧ q = ∞ ∨ 0 < p.toReal ∧ 0 < q.toReal ∧ p.toReal <= q.toReal := by
  rcases eq_or_lt_of_le (bot_le : 0 <= p) with ((rfl : 0 = p) | (hp : 0 < p))
  · simpa using q.trichotomy
  rcases eq_or_lt_of_le (le_top : q <= ∞) with (rfl | hq)
  · simpa using p.trichotomy
  have hq' : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq
  simp [ENNReal.toReal_mono hq.ne hpq, ENNReal.toReal_pos_iff, hp, hp', hq', hq]

/--
theorem `dichotomy` / 定理 `dichotomy`

English:
theorem dichotomy
  given: (p : Real>=0∞) [Fact (1 <= p)]
  statement: p = ∞ ∨ 1 <= p.toReal
  proof: haveI : p = ⊤ ∨ 0 < p.toReal ∧ 1 <= p.toReal := by
    simpa using ENNReal.trichotomy₂ (Fact.out : 1 <= p)
  this.imp_right fun h => h.2

中文:
定理 dichotomy
  条件: (p : 实数>=0∞) [Fact (1 <= p)]
  结论: p = ∞ ∨ 1 <= p.to实数
  证明: haveI : p = ⊤ ∨ 0 < p.toReal ∧ 1 <= p.toReal := by
    simpa using ENNReal.trichotomy₂ (Fact.out : 1 <= p)
  this.imp_right fun h => h.2
-/
protected theorem dichotomy (p : Real>=0∞) [Fact (1 <= p)] : p = ∞ ∨ 1 <= p.toReal :=
  haveI : p = ⊤ ∨ 0 < p.toReal ∧ 1 <= p.toReal := by
    simpa using ENNReal.trichotomy₂ (Fact.out : 1 <= p)
  this.imp_right fun h => h.2

/--
theorem `toReal_pos_iff_ne_top` / 定理 `toReal_pos_iff_ne_top`

English:
theorem toReal_pos_iff_ne_top
  given: (p : Real>=0∞) [Fact (1 <= p)]
  statement: 0 < p.toReal ↔ p != ∞
  proof: ⟨fun h hp =>
    have : (0 : Real) != 0 := toReal_top ▸ (hp ▸ h.ne : 0 != ∞.toReal)
    this rfl,
    fun h => zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩

中文:
定理 toReal_pos_iff_ne_top
  条件: (p : 实数>=0∞) [Fact (1 <= p)]
  结论: 0 < p.to实数 ↔ p != ∞
  证明: ⟨fun h hp =>
    have : (0 : Real) != 0 := toReal_top ▸ (hp ▸ h.ne : 0 != ∞.toReal)
    this rfl,
    fun h => zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩

Depends on / 依赖: dichotomy, h.ne, p.dichotomy.resolve_left, resolve_left, toReal, toReal_top, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem toReal_pos_iff_ne_top (p : Real>=0∞) [Fact (1 <= p)] : 0 < p.toReal ↔ p != ∞ :=
  ⟨fun h hp =>
    have : (0 : Real) != 0 := toReal_top ▸ (hp ▸ h.ne : 0 != ∞.toReal)
    this rfl,
    fun h => zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩

end Real

end ENNReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `ENNReal.ofReal`. -/
@[positivity ENNReal.ofReal _]
meta def evalENNRealOfReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real>=0∞), ~q(ENNReal.ofReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(Iff.mpr (@ENNReal.ofReal_pos $a) $pa))
    | _ => pure .none
  | _, _, _ => throwError "not ENNReal.ofReal"
end Mathlib.Meta.Positivity
