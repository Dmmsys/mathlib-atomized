/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.ENat.Basic

/-!
# Powers of extended natural numbers

We define the power of an extended natural `x : ℕ∞` by another extended natural `y : ℕ∞`. The
definition is chosen such that `x ^ y` is the cardinality of `α → β`, when `β` has cardinality `x`
and `α` has cardinality `y`:

* When `y` is finite, it coincides with the exponentiation by natural numbers (e.g. `⊤ ^ 0 = 1`).
* We set `0 ^ ⊤ = 0`, `1 ^ ⊤ = 1` and `x ^ ⊤ = ⊤` for `x > 1`.

## Naming convention

The quantity `x ^ y` for `x`, `y : ℕ∞` is defined as a `Pow` instance. It is called `epow` in
lemmas' names.
-/

@[expose] public section

namespace ENat

variable {x y z : Nat∞}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow Nat∞ Nat∞

中文:
实例 :
  签名: 幂 自然数∞ 自然数∞
-/
instance : Pow Nat∞ Nat∞ where
  pow
    | x, some y => x ^ y
    | x, ⊤ => if x = 0 then 0 else if x = 1 then 1 else ⊤

/--
lemma `epow_def` / 引理 `epow_def`

English:
lemma epow_def
  given: {x y : Nat∞}
  proof: by
  cases y with
  | top => simp only [lt_self_iff_false, ↓reduceIte]; rfl
  | coe n => simp only [natCast_lt_top, ↓reduceIte, toNat_natCast]; rfl

@[simp, norm_cast]

中文:
引理 epow_def
  条件: {x y : 自然数∞}
  证明: by
  cases y with
  | top => simp only [lt_self_iff_false, ↓reduceIte]; rfl
  | coe n => simp only [natCast_lt_top, ↓reduceIte, toNat_natCast]; rfl

@[simp, norm_cast]

Depends on / 依赖: lt_self_iff_false, natCast_lt_top, reduceIte, toNat_natCast
-/
lemma epow_def {x y : Nat∞} :
    x ^ y = if y < ⊤ then x ^ y.toNat else if x = 0 then 0 else if x = 1 then 1 else ⊤ := by
  cases y with
  | top => simp only [lt_self_iff_false, ↓reduceIte]; rfl
  | coe n => simp only [natCast_lt_top, ↓reduceIte, toNat_natCast]; rfl

@[simp, norm_cast]
/--
lemma `epow_natCast` / 引理 `epow_natCast`

English:
lemma epow_natCast
  given: {y : Nat}
  statement: x ^ (y : Nat∞) = x ^ y
  proof: rfl

@[simp]

中文:
引理 epow_natCast
  条件: {y : 自然数}
  结论: x ^ (y : 自然数∞) = x ^ y
  证明: rfl

@[simp]
-/
lemma epow_natCast {y : Nat} : x ^ (y : Nat∞) = x ^ y := rfl

@[simp]
/--
lemma `zero_epow_top` / 引理 `zero_epow_top`

English:
lemma zero_epow_top
  statement: (0 : Nat∞) ^ (⊤ : Nat∞) = 0
  proof: rfl

中文:
引理 zero_epow_top
  结论: (0 : 自然数∞) ^ (⊤ : 自然数∞) = 0
  证明: rfl
-/
lemma zero_epow_top : (0 : Nat∞) ^ (⊤ : Nat∞) = 0 := rfl

/--
lemma `zero_epow` / 引理 `zero_epow`

English:
lemma zero_epow
  given: (h : y != 0)
  statement: (0 : Nat∞) ^ y = 0
  proof: by
  induction y with
  | top => exact zero_epow_top
  | coe y => rwa [epow_natCast, pow_eq_zero_iff', eq_self 0, true_and, ← y.cast_ne_zero (R := Nat∞)]

@[simp]

中文:
引理 zero_epow
  条件: (h : y != 0)
  结论: (0 : 自然数∞) ^ y = 0
  证明: by
  induction y with
  | top => exact zero_epow_top
  | coe y => rwa [epow_natCast, pow_eq_zero_iff', eq_self 0, true_and, ← y.cast_ne_zero (R := Nat∞)]

@[simp]

Depends on / 依赖: cast_ne_zero, epow_natCast, eq_self, pow_eq_zero_iff, true_and, y.cast_ne_zero, zero_epow_top
-/
lemma zero_epow (h : y != 0) : (0 : Nat∞) ^ y = 0 := by
  induction y with
  | top => exact zero_epow_top
  | coe y => rwa [epow_natCast, pow_eq_zero_iff', eq_self 0, true_and, ← y.cast_ne_zero (R := Nat∞)]

@[simp]
/--
lemma `one_epow` / 引理 `one_epow`

English:
lemma one_epow
  statement: (1 : Nat∞) ^ y = 1
  proof: by
  induction y with
  | top => rfl
  | coe y => rw [epow_natCast, one_pow]

@[simp]

中文:
引理 one_epow
  结论: (1 : 自然数∞) ^ y = 1
  证明: by
  induction y with
  | top => rfl
  | coe y => rw [epow_natCast, one_pow]

@[simp]

Depends on / 依赖: epow_natCast, one_pow
-/
lemma one_epow : (1 : Nat∞) ^ y = 1 := by
  induction y with
  | top => rfl
  | coe y => rw [epow_natCast, one_pow]

@[simp]
/--
lemma `top_epow_top` / 引理 `top_epow_top`

English:
lemma top_epow_top
  statement: (⊤ : Nat∞) ^ (⊤ : Nat∞) = ⊤
  proof: rfl

中文:
引理 top_epow_top
  结论: (⊤ : 自然数∞) ^ (⊤ : 自然数∞) = ⊤
  证明: rfl
-/
lemma top_epow_top : (⊤ : Nat∞) ^ (⊤ : Nat∞) = ⊤ := rfl

/--
lemma `top_epow` / 引理 `top_epow`

English:
lemma top_epow
  given: (h : y != 0)
  statement: (⊤ : Nat∞) ^ y = ⊤
  proof: by
  induction y with
  | top => exact top_epow_top
  | coe y => rwa [epow_natCast, pow_eq_top_iff, eq_self ⊤, true_and, ← y.cast_ne_zero (R := Nat∞)]

@[simp]

中文:
引理 top_epow
  条件: (h : y != 0)
  结论: (⊤ : 自然数∞) ^ y = ⊤
  证明: by
  induction y with
  | top => exact top_epow_top
  | coe y => rwa [epow_natCast, pow_eq_top_iff, eq_self ⊤, true_and, ← y.cast_ne_zero (R := Nat∞)]

@[simp]

Depends on / 依赖: cast_ne_zero, epow_natCast, eq_self, pow_eq_top_iff, top_epow_top, true_and, y.cast_ne_zero
-/
lemma top_epow (h : y != 0) : (⊤ : Nat∞) ^ y = ⊤ := by
  induction y with
  | top => exact top_epow_top
  | coe y => rwa [epow_natCast, pow_eq_top_iff, eq_self ⊤, true_and, ← y.cast_ne_zero (R := Nat∞)]

@[simp]
/--
lemma `epow_zero` / 引理 `epow_zero`

English:
lemma epow_zero
  statement: x ^ (0 : Nat∞) = 1
  proof: by
  rw [← natCast_zero]; rw [epow_natCast]; rw [pow_zero]

@[simp]

中文:
引理 epow_zero
  结论: x ^ (0 : 自然数∞) = 1
  证明: by
  rw [← natCast_zero]; rw [epow_natCast]; rw [pow_zero]

@[simp]

Depends on / 依赖: epow_natCast, natCast_zero, pow_zero
-/
lemma epow_zero : x ^ (0 : Nat∞) = 1 := by
  rw [← natCast_zero]; rw [epow_natCast]; rw [pow_zero]

@[simp]
/--
lemma `epow_one` / 引理 `epow_one`

English:
lemma epow_one
  statement: x ^ (1 : Nat∞) = x
  proof: by
  rw [← natCast_one]; rw [epow_natCast]; rw [pow_one]

中文:
引理 epow_one
  结论: x ^ (1 : 自然数∞) = x
  证明: by
  rw [← natCast_one]; rw [epow_natCast]; rw [pow_one]

Depends on / 依赖: epow_natCast, natCast_one, pow_one
-/
lemma epow_one : x ^ (1 : Nat∞) = x := by
  rw [← natCast_one]; rw [epow_natCast]; rw [pow_one]

/--
lemma `epow_top` / 引理 `epow_top`

English:
lemma epow_top
  given: (h : 1 < x)
  statement: x ^ (⊤ : Nat∞) = ⊤
  proof: by
  have : (0 : Nat∞) <= 1 := zero_le_one
  rw [epow_def]; rw [if_neg]; rw [if_neg]; rw [if_neg] <;> grind

中文:
引理 epow_top
  条件: (h : 1 < x)
  结论: x ^ (⊤ : 自然数∞) = ⊤
  证明: by
  have : (0 : Nat∞) <= 1 := zero_le_one
  rw [epow_def]; rw [if_neg]; rw [if_neg]; rw [if_neg] <;> grind

Depends on / 依赖: epow_def, if_neg, zero_le_one
-/
lemma epow_top (h : 1 < x) : x ^ (⊤ : Nat∞) = ⊤ := by
  have : (0 : Nat∞) <= 1 := zero_le_one
  rw [epow_def]; rw [if_neg]; rw [if_neg]; rw [if_neg] <;> grind

/--
lemma `epow_right_mono` / 引理 `epow_right_mono`

English:
lemma epow_right_mono
  given: (h : x != 0)
  statement: Monotone (fun y : Nat∞ => x ^ y)
  proof: by
  intro y z y_z
  induction y
  · rw [top_le_iff.1 y_z]
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · exact (h (Order.lt_one_iff.1 x_0)).rec
    · simp only [one_epow, le_refl]
    · simp only [epow_top x_2, le_top]
  · exact pow_right_mono₀ (Order.one_le_iff_ne_zero.2 h) 

中文:
引理 epow_right_mono
  条件: (h : x != 0)
  结论: 递增 (fun y : 自然数∞ => x ^ y)
  证明: by
  intro y z y_z
  induction y
  · rw [top_le_iff.1 y_z]
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · exact (h (Order.lt_one_iff.1 x_0)).rec
    · simp only [one_epow, le_refl]
    · simp only [epow_top x_2, le_top]
  · exact pow_right_mono₀ (Order.one_le_iff_ne_zero.2 h) 

Depends on / 依赖: Nat.cast_le, Order.lt_one_iff, Order.one_le_iff_ne_zero, cast_le, epow_top, le_refl, le_top, lt_one_iff, lt_trichotomy, one_epow, one_le_iff_ne_zero, top_le_iff
-/
lemma epow_right_mono (h : x != 0) : Monotone (fun y : Nat∞ => x ^ y) := by
  intro y z y_z
  induction y
  · rw [top_le_iff.1 y_z]
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · exact (h (Order.lt_one_iff.1 x_0)).rec
    · simp only [one_epow, le_refl]
    · simp only [epow_top x_2, le_top]
  · exact pow_right_mono₀ (Order.one_le_iff_ne_zero.2 h) (Nat.cast_le.1 y_z)

/--
lemma `one_le_epow` / 引理 `one_le_epow`

English:
lemma one_le_epow
  given: (h : x != 0)
  statement: 1 <= x ^ y
  proof: by
  simpa using epow_right_mono h zero_le

中文:
引理 one_le_epow
  条件: (h : x != 0)
  结论: 1 <= x ^ y
  证明: by
  simpa using epow_right_mono h zero_le

Depends on / 依赖: epow_right_mono, zero_le
-/
lemma one_le_epow (h : x != 0) : 1 <= x ^ y := by
  simpa using epow_right_mono h zero_le

/--
lemma `epow_pos` / 引理 `epow_pos`

English:
lemma epow_pos
  given: (h : x != 0)
  statement: 0 < x ^ y
  proof: by
  rw [← Order.one_le_iff_pos]; exact one_le_epow h

中文:
引理 epow_pos
  条件: (h : x != 0)
  结论: 0 < x ^ y
  证明: by
  rw [← Order.one_le_iff_pos]; exact one_le_epow h

Depends on / 依赖: Order.one_le_iff_pos, one_le_epow, one_le_iff_pos
-/
lemma epow_pos (h : x != 0) : 0 < x ^ y := by
  rw [← Order.one_le_iff_pos]; exact one_le_epow h

/--
lemma `epow_left_mono` / 引理 `epow_left_mono`

English:
lemma epow_left_mono
  statement: Monotone (fun x : Nat∞ => x ^ y)
  proof: by
  intro x z x_z
  simp only
  induction y
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · rw [Order.lt_one_iff.1 x_0, zero_epow_top]; exact bot_le
    · rw [one_epow]; exact one_le_epow (Order.one_le_iff_ne_zero.1 x_z)
    · rw [epow_top (x_2.trans_le x_z)]; exact le_top
  · simp only [ep

中文:
引理 epow_left_mono
  结论: 递增 (fun x : 自然数∞ => x ^ y)
  证明: by
  intro x z x_z
  simp only
  induction y
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · rw [Order.lt_one_iff.1 x_0, zero_epow_top]; exact bot_le
    · rw [one_epow]; exact one_le_epow (Order.one_le_iff_ne_zero.1 x_z)
    · rw [epow_top (x_2.trans_le x_z)]; exact le_top
  · simp only [ep

Depends on / 依赖: Order.lt_one_iff, Order.one_le_iff_ne_zero, bot_le, epow_natCast, epow_top, le_top, lt_one_iff, lt_trichotomy, one_epow, one_le_epow, one_le_iff_ne_zero, pow_left_mono, trans_le, x_2.trans_le, zero_epow_top
-/
lemma epow_left_mono : Monotone (fun x : Nat∞ => x ^ y) := by
  intro x z x_z
  simp only
  induction y
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · rw [Order.lt_one_iff.1 x_0, zero_epow_top]; exact bot_le
    · rw [one_epow]; exact one_le_epow (Order.one_le_iff_ne_zero.1 x_z)
    · rw [epow_top (x_2.trans_le x_z)]; exact le_top
  · simp only [epow_natCast, (pow_left_mono _) x_z]

/--
lemma `epow_eq_zero_iff` / 引理 `epow_eq_zero_iff`

English:
lemma epow_eq_zero_iff
  statement: x ^ y = 0 ↔ x = 0 ∧ y != 0
  proof: by
  refine ⟨fun h => ⟨?_, fun y_0 => ?_⟩, fun h => h.1.symm ▸ zero_epow h.2⟩
  · contrapose! h
    exact (epow_pos h).ne'
  · rw [y_0, epow_zero] at h; contradiction

中文:
引理 epow_eq_zero_iff
  结论: x ^ y = 0 ↔ x = 0 ∧ y != 0
  证明: by
  refine ⟨fun h => ⟨?_, fun y_0 => ?_⟩, fun h => h.1.symm ▸ zero_epow h.2⟩
  · contrapose! h
    exact (epow_pos h).ne'
  · rw [y_0, epow_zero] at h; contradiction

Depends on / 依赖: contrapose, epow_pos, epow_zero, zero_epow
-/
lemma epow_eq_zero_iff : x ^ y = 0 ↔ x = 0 ∧ y != 0 := by
  refine ⟨fun h => ⟨?_, fun y_0 => ?_⟩, fun h => h.1.symm ▸ zero_epow h.2⟩
  · contrapose! h
    exact (epow_pos h).ne'
  · rw [y_0, epow_zero] at h; contradiction

/--
lemma `epow_eq_one_iff` / 引理 `epow_eq_one_iff`

English:
lemma epow_eq_one_iff
  statement: x ^ y = 1 ↔ x = 1 ∨ y = 0
  proof: by
  refine ⟨fun h => or_iff_not_imp_right.2 fun y_0 => ?_, fun h => by rcases h with h | h <;> simp [h]⟩
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0] at h; contradiction
  · rfl
  · have := epow_right_mono x_2.ne_zero (Order.one_le_iff_ne_zero.2 y_0

中文:
引理 epow_eq_one_iff
  结论: x ^ y = 1 ↔ x = 1 ∨ y = 0
  证明: by
  refine ⟨fun h => or_iff_not_imp_right.2 fun y_0 => ?_, fun h => by rcases h with h | h <;> simp [h]⟩
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0] at h; contradiction
  · rfl
  · have := epow_right_mono x_2.ne_zero (Order.one_le_iff_ne_zero.2 y_0

Depends on / 依赖: Order.lt_one_iff, Order.one_le_iff_ne_zero, epow_one, epow_right_mono, lt_one_iff, lt_trichotomy, ne_zero, not_lt_of_ge, one_le_iff_ne_zero, or_iff_not_imp_right, x_2.ne_zero, zero_epow
-/
lemma epow_eq_one_iff : x ^ y = 1 ↔ x = 1 ∨ y = 0 := by
  refine ⟨fun h => or_iff_not_imp_right.2 fun y_0 => ?_, fun h => by rcases h with h | h <;> simp [h]⟩
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0] at h; contradiction
  · rfl
  · have := epow_right_mono x_2.ne_zero (Order.one_le_iff_ne_zero.2 y_0)
    simp only [epow_one, h] at this
    exact (not_lt_of_ge this x_2).rec

/--
lemma `epow_add` / 引理 `epow_add`

English:
lemma epow_add
  statement: x ^ (y + z) = x ^ y * x ^ z
  proof: by
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0]
    rcases eq_zero_or_pos y with rfl | y_0
    · simp only [zero_add, epow_zero, one_mul]
    · rw [zero_epow y_0.ne.symm, zero_mul]
      exact zero_epow (add_pos_of_pos_of_nonneg y_0 bot_le).ne.symm
  · simp only [o

中文:
引理 epow_add
  结论: x ^ (y + z) = x ^ y * x ^ z
  证明: by
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0]
    rcases eq_zero_or_pos y with rfl | y_0
    · simp only [zero_add, epow_zero, one_mul]
    · rw [zero_epow y_0.ne.symm, zero_mul]
      exact zero_epow (add_pos_of_pos_of_nonneg y_0 bot_le).ne.symm
  · simp only [o

Depends on / 依赖: Nat.cast_add, Order.lt_one_iff, add_pos_of_pos_of_nonneg, add_top, bot_le, cast_add, epow_natCas, epow_pos, epow_top, epow_zero, eq_zero_or_pos, lt_one_iff, lt_trichotomy, mul_one, mul_top, ne.symm, ne_zero, one_epow, one_mul, top_add
-/
lemma epow_add : x ^ (y + z) = x ^ y * x ^ z := by
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0]
    rcases eq_zero_or_pos y with rfl | y_0
    · simp only [zero_add, epow_zero, one_mul]
    · rw [zero_epow y_0.ne.symm, zero_mul]
      exact zero_epow (add_pos_of_pos_of_nonneg y_0 bot_le).ne.symm
  · simp only [one_epow, mul_one]
  · induction y
    · rw [top_add, epow_top x_2, top_mul]
      exact (epow_pos x_2.ne_zero).ne'
    induction z
    · rw [add_top, epow_top x_2, mul_top]
      exact (epow_pos x_2.ne_zero).ne'
    simp only [← Nat.cast_add, epow_natCast, pow_add x]

/--
lemma `mul_epow` / 引理 `mul_epow`

English:
lemma mul_epow
  statement: (x * y) ^ z = x ^ z * y ^ z
  proof: by
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · simp only [Order.lt_one_iff.1 x_0, zero_mul, zero_epow_top]
    · simp only [one_mul, one_epow]
    · rcases lt_trichotomy y 1 with y_0 | rfl | y_2
      · simp only [Order.lt_one_iff.1 y_0, mul_zero, zero_epow_top]
      · sim

中文:
引理 mul_epow
  结论: (x * y) ^ z = x ^ z * y ^ z
  证明: by
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · simp only [Order.lt_one_iff.1 x_0, zero_mul, zero_epow_top]
    · simp only [one_mul, one_epow]
    · rcases lt_trichotomy y 1 with y_0 | rfl | y_2
      · simp only [Order.lt_one_iff.1 y_0, mul_zero, zero_epow_top]
      · sim

Depends on / 依赖: Order.lt_one_iff, epow_natCast, epow_top, lt_one_iff, lt_trichotomy, mul_pow, mul_top, mul_zero, one_epow, one_lt_mul, one_mul, top_ne_zero, x_2.le, zero_epow_top, zero_mul
-/
lemma mul_epow : (x * y) ^ z = x ^ z * y ^ z := by
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · simp only [Order.lt_one_iff.1 x_0, zero_mul, zero_epow_top]
    · simp only [one_mul, one_epow]
    · rcases lt_trichotomy y 1 with y_0 | rfl | y_2
      · simp only [Order.lt_one_iff.1 y_0, mul_zero, zero_epow_top]
      · simp
      · rw [epow_top x_2, epow_top y_2, mul_top top_ne_zero]
        exact epow_top (one_lt_mul x_2.le y_2)
  · simp only [epow_natCast, mul_pow x y]

/--
lemma `epow_mul` / 引理 `epow_mul`

English:
lemma epow_mul
  statement: x ^ (y * z) = (x ^ y) ^ z
  proof: by
  rcases eq_or_ne y 0 with y_0 | y_0
  · simp [y_0]
  rcases eq_or_ne z 0 with z_0 | z_0
  · simp [z_0]
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0, zero_epow z_0, zero_epow (mul_ne_zero y_0 z_0)]
  · simp only [one_epow]
  · induction y
    · rw 

中文:
引理 epow_mul
  结论: x ^ (y * z) = (x ^ y) ^ z
  证明: by
  rcases eq_or_ne y 0 with y_0 | y_0
  · simp [y_0]
  rcases eq_or_ne z 0 with z_0 | z_0
  · simp [z_0]
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0, zero_epow z_0, zero_epow (mul_ne_zero y_0 z_0)]
  · simp only [one_epow]
  · induction y
    · rw 

Depends on / 依赖: Nat.cast_mul, Order.lt_one_iff, Order.one_le_iff_ne_zero, cast_mul, epow_right_mono, epow_top, eq_or_ne, lt_one_iff, lt_trichotomy, mul_ne_zero, mul_top, ne_zero, one_epow, one_le_iff_ne_zero, top_epow, top_mul, trans_lt, x_2.ne_zero, zero_epow
-/
lemma epow_mul : x ^ (y * z) = (x ^ y) ^ z := by
  rcases eq_or_ne y 0 with y_0 | y_0
  · simp [y_0]
  rcases eq_or_ne z 0 with z_0 | z_0
  · simp [z_0]
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0, zero_epow z_0, zero_epow (mul_ne_zero y_0 z_0)]
  · simp only [one_epow]
  · induction y
    · rw [top_mul z_0, epow_top x_2, top_epow z_0]
    induction z
    · rw [mul_top y_0, epow_top x_2, epow_top]
      apply (epow_right_mono x_2.ne_zero (Order.one_le_iff_ne_zero.2 y_0)).trans_lt'
      simp [x_2]
    · simp only [← Nat.cast_mul, epow_natCast, pow_mul x]

end ENat
