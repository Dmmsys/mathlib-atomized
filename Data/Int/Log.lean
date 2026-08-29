/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Log

/-!
# Integer logarithms in a field with respect to a natural base

This file defines two `ℤ`-valued analogs of the logarithm of `r : R` with base `b : ℕ`:

* `Int.log b r`: Lower logarithm, or floor **log**. Greatest `k` such that `↑b^k ≤ r`.
* `Int.clog b r`: Upper logarithm, or **c**eil **log**. Least `k` such that `r ≤ ↑b^k`.

Note that `Int.log` gives the position of the left-most non-zero digit:
```lean
#eval (Int.log 10 (0.09 : ℚ), Int.log 10 (0.10 : ℚ), Int.log 10 (0.11 : ℚ))
-- (-2, -1, -1)
#eval (Int.log 10 (9 : ℚ), Int.log 10 (10 : ℚ), Int.log 10 (11 : ℚ))
-- (0, 1, 1)
```
which means it can be used for computing digit expansions
```lean
import Data.Fin.VecNotation
import Mathlib.Data.Rat.Floor

def digits (b : ℕ) (q : ℚ) (n : ℕ) : ℕ :=
  ⌊q * ((b : ℚ) ^ (n - Int.log b q))⌋₊ % b

#eval digits 10 (1/7) ∘ ((↑) : Fin 8 → ℕ)
-- ![1, 4, 2, 8, 5, 7, 1, 4]
```

## Main results

* For `Int.log`:
  * `Int.zpow_log_le_self`, `Int.lt_zpow_succ_log_self`: the bounds formed by `Int.log`,
    `(b : R) ^ log b r ≤ r < (b : R) ^ (log b r + 1)`.
  * `Int.zpow_log_gi`: the Galois coinsertion between `zpow` and `Int.log`.
* For `Int.clog`:
  * `Int.zpow_pred_clog_lt_self`, `Int.self_le_zpow_clog`: the bounds formed by `Int.clog`,
    `(b : R) ^ (clog b r - 1) < r ≤ (b : R) ^ clog b r`.
  * `Int.clog_zpow_gi`: the Galois insertion between `Int.clog` and `zpow`.
* `Int.neg_log_inv_eq_clog`, `Int.neg_clog_inv_eq_log`: the link between the two definitions.
-/

@[expose] public section

assert_not_exists Finset

variable {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

namespace Int

/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: (b : Nat) (r : R)
  body: if 1 <= r then Nat.log b ⌊r⌋₊ else -Nat.clog b ⌈r⁻¹⌉₊

omit [IsStrictOrderedRing R] in

中文:
定义 log
  签名: (b : 自然数) (r : R)
  定义体: if 1 <= r then Nat.log b ⌊r⌋₊ else -Nat.clog b ⌈r⁻¹⌉₊

omit [IsStrictOrderedRing R] in

Depends on / 依赖: Nat.clog, Nat.log
-/
def log (b : Nat) (r : R) : Int :=
  if 1 <= r then Nat.log b ⌊r⌋₊ else -Nat.clog b ⌈r⁻¹⌉₊

omit [IsStrictOrderedRing R] in
/--
theorem `log_of_one_le_right` / 定理 `log_of_one_le_right`

English:
theorem log_of_one_le_right
  given: (b : Nat) {r : R} (hr : 1 <= r)
  statement: log b r = Nat.log b ⌊r⌋₊
  proof: if_pos hr

中文:
定理 log_of_one_le_right
  条件: (b : 自然数) {r : R} (hr : 1 <= r)
  结论: log b r = 自然数.log b ⌊r⌋₊
  证明: if_pos hr

Depends on / 依赖: if_pos
-/
theorem log_of_one_le_right (b : Nat) {r : R} (hr : 1 <= r) : log b r = Nat.log b ⌊r⌋₊ :=
  if_pos hr

/--
theorem `log_of_right_le_one` / 定理 `log_of_right_le_one`

English:
theorem log_of_right_le_one
  given: (b : Nat) {r : R} (hr : r <= 1)
  statement: log b r = -Nat.clog b ⌈r⁻¹⌉₊
  proof: by
  obtain rfl | hr := hr.eq_or_lt
  · rw [log, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right, Nat.clog_one_right,
      Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_ge

@[simp, norm_cast]

中文:
定理 log_of_right_le_one
  条件: (b : 自然数) {r : R} (hr : r <= 1)
  结论: log b r = -自然数.clog b ⌈r⁻¹⌉₊
  证明: by
  obtain rfl | hr := hr.eq_or_lt
  · rw [log, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right, Nat.clog_one_right,
      Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_ge

@[simp, norm_cast]

Depends on / 依赖: Int.ofNat_zero, Nat.ceil_one, Nat.clog_one_right, Nat.floor_one, Nat.log_one_right, ceil_one, clog_one_right, eq_or_lt, floor_one, hr.eq_or_lt, hr.not_ge, if_neg, if_pos, inv_one, log_one_right, neg_zero, not_ge, ofNat_zero
-/
theorem log_of_right_le_one (b : Nat) {r : R} (hr : r <= 1) : log b r = -Nat.clog b ⌈r⁻¹⌉₊ := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [log, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right, Nat.clog_one_right,
      Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_ge

@[simp, norm_cast]
/--
theorem `log_natCast` / 定理 `log_natCast`

English:
theorem log_natCast
  given: (b : Nat) (n : Nat)
  statement: log b (n : R) = Nat.log b n
  proof: by
  cases n
  · simp [log_of_right_le_one]
  · rw [log_of_one_le_right, Nat.floor_natCast]
    simp

@[simp]

中文:
定理 log_natCast
  条件: (b : 自然数) (n : 自然数)
  结论: log b (n : R) = 自然数.log b n
  证明: by
  cases n
  · simp [log_of_right_le_one]
  · rw [log_of_one_le_right, Nat.floor_natCast]
    simp

@[simp]

Depends on / 依赖: Nat.floor_natCast, floor_natCast, log_of_one_le_right, log_of_right_le_one
-/
theorem log_natCast (b : Nat) (n : Nat) : log b (n : R) = Nat.log b n := by
  cases n
  · simp [log_of_right_le_one]
  · rw [log_of_one_le_right, Nat.floor_natCast]
    simp

@[simp]
/--
theorem `log_ofNat` / 定理 `log_ofNat`

English:
theorem log_ofNat
  given: (b : Nat) (n : Nat) [n.AtLeastTwo]
  proof: log_natCast b n

中文:
定理 log_of自然数
  条件: (b : 自然数) (n : 自然数) [n.AtLeastTwo]
  证明: log_natCast b n

Depends on / 依赖: log_natCast
-/
theorem log_ofNat (b : Nat) (n : Nat) [n.AtLeastTwo] :
    log b (ofNat(n) : R) = Nat.log b ofNat(n) :=
  log_natCast b n

/--
theorem `log_of_left_le_one` / 定理 `log_of_left_le_one`

English:
theorem log_of_left_le_one
  given: {b : Nat} (hb : b <= 1) (r : R)
  statement: log b r = 0
  proof: by
  rcases le_total 1 r with h | h
  · rw [log_of_one_le_right _ h, Nat.log_of_left_le_one hb, Int.ofNat_zero]
  · rw [log_of_right_le_one _ h, Nat.clog_of_left_le_one hb, Int.ofNat_zero, neg_zero]

中文:
定理 log_of_left_le_one
  条件: {b : 自然数} (hb : b <= 1) (r : R)
  结论: log b r = 0
  证明: by
  rcases le_total 1 r with h | h
  · rw [log_of_one_le_right _ h, Nat.log_of_left_le_one hb, Int.ofNat_zero]
  · rw [log_of_right_le_one _ h, Nat.clog_of_left_le_one hb, Int.ofNat_zero, neg_zero]

Depends on / 依赖: Int.ofNat_zero, Nat.clog_of_left_le_one, Nat.log_of_left_le_one, clog_of_left_le_one, le_total, log_of_left_le_one, log_of_one_le_right, log_of_right_le_one, neg_zero, ofNat_zero
-/
theorem log_of_left_le_one {b : Nat} (hb : b <= 1) (r : R) : log b r = 0 := by
  rcases le_total 1 r with h | h
  · rw [log_of_one_le_right _ h, Nat.log_of_left_le_one hb, Int.ofNat_zero]
  · rw [log_of_right_le_one _ h, Nat.clog_of_left_le_one hb, Int.ofNat_zero, neg_zero]

/--
theorem `log_of_right_le_zero` / 定理 `log_of_right_le_zero`

English:
theorem log_of_right_le_zero
  given: (b : Nat) {r : R} (hr : r <= 0)
  statement: log b r = 0
  proof: by
  rw [log_of_right_le_one _ (hr.trans zero_le_one)]; rw [Nat.clog_of_right_le_one ((Nat.ceil_eq_zero.mpr <| inv_nonpos.2 hr).trans_le zero_le_one)]; rw [Int.ofNat_zero]; rw [neg_zero]

中文:
定理 log_of_right_le_zero
  条件: (b : 自然数) {r : R} (hr : r <= 0)
  结论: log b r = 0
  证明: by
  rw [log_of_right_le_one _ (hr.trans zero_le_one)]; rw [Nat.clog_of_right_le_one ((Nat.ceil_eq_zero.mpr <| inv_nonpos.2 hr).trans_le zero_le_one)]; rw [Int.ofNat_zero]; rw [neg_zero]

Depends on / 依赖: Int.ofNat_zero, Nat.ceil_eq_zero.mpr, Nat.clog_of_right_le_one, ceil_eq_zero, clog_of_right_le_one, hr.trans, inv_nonpos, log_of_right_le_one, neg_zero, ofNat_zero, trans_le, zero_le_one
-/
theorem log_of_right_le_zero (b : Nat) {r : R} (hr : r <= 0) : log b r = 0 := by
  rw [log_of_right_le_one _ (hr.trans zero_le_one)]; rw [Nat.clog_of_right_le_one ((Nat.ceil_eq_zero.mpr <| inv_nonpos.2 hr).trans_le zero_le_one)]; rw [Int.ofNat_zero]; rw [neg_zero]

/--
theorem `zpow_log_le_self` / 定理 `zpow_log_le_self`

English:
theorem zpow_log_le_self
  given: {b : Nat} {r : R} (hb : 1 < b) (hr : 0 < r)
  statement: (b : R) ^ log b r <= r
  proof: by
  rcases le_total 1 r with hr1 | hr1
  · rw [log_of_one_le_right _ hr1]
    rw [zpow_natCast]; rw [← Nat.cast_pow]; rw [← Nat.le_floor_iff hr.le]
    exact Nat.pow_log_le_self b (Nat.floor_pos.mpr hr1).ne'
  · rw [log_of_right_le_one _ hr1, zpow_neg]
    exact_mod_cast inv_le_of_inv_le₀ hr (Nat.c

中文:
定理 zpow_log_le_self
  条件: {b : 自然数} {r : R} (hb : 1 < b) (hr : 0 < r)
  结论: (b : R) ^ log b r <= r
  证明: by
  rcases le_total 1 r with hr1 | hr1
  · rw [log_of_one_le_right _ hr1]
    rw [zpow_natCast]; rw [← Nat.cast_pow]; rw [← Nat.le_floor_iff hr.le]
    exact Nat.pow_log_le_self b (Nat.floor_pos.mpr hr1).ne'
  · rw [log_of_right_le_one _ hr1, zpow_neg]
    exact_mod_cast inv_le_of_inv_le₀ hr (Nat.c

Depends on / 依赖: Nat.cast_pow, Nat.ceil_le, Nat.floor_pos.mpr, Nat.le_floor_iff, Nat.le_pow_clog, Nat.pow_log_le_self, cast_pow, ceil_le, floor_pos, hr.le, le_floor_iff, le_pow_clog, le_total, log_of_one_le_right, log_of_right_le_one, pow_log_le_self, zpow_natCast, zpow_neg
-/
theorem zpow_log_le_self {b : Nat} {r : R} (hb : 1 < b) (hr : 0 < r) : (b : R) ^ log b r <= r := by
  rcases le_total 1 r with hr1 | hr1
  · rw [log_of_one_le_right _ hr1]
    rw [zpow_natCast]; rw [← Nat.cast_pow]; rw [← Nat.le_floor_iff hr.le]
    exact Nat.pow_log_le_self b (Nat.floor_pos.mpr hr1).ne'
  · rw [log_of_right_le_one _ hr1, zpow_neg]
    exact_mod_cast inv_le_of_inv_le₀ hr (Nat.ceil_le.1 <| Nat.le_pow_clog hb _)

/--
theorem `lt_zpow_succ_log_self` / 定理 `lt_zpow_succ_log_self`

English:
theorem lt_zpow_succ_log_self
  given: {b : Nat} (hb : 1 < b) (r : R)
  statement: r < (b : R) ^ (log b r + 1)
  proof: by
  rcases le_or_gt r 0 with hr | hr
  · rw [log_of_right_le_zero _ hr, zero_add, zpow_one]
    exact hr.trans_lt (zero_lt_one.trans_le <| mod_cast hb.le)
  rcases le_or_gt 1 r with hr1 | hr1
  · rw [log_of_one_le_right _ hr1, Int.ofNat_add_one_out]
exact_mod_cast Nat.lt_of_floor_lt Nat.lt_pow_succ

中文:
定理 lt_zpow_succ_log_self
  条件: {b : 自然数} (hb : 1 < b) (r : R)
  结论: r < (b : R) ^ (log b r + 1)
  证明: by
  rcases le_or_gt r 0 with hr | hr
  · rw [log_of_right_le_zero _ hr, zero_add, zpow_one]
    exact hr.trans_lt (zero_lt_one.trans_le <| mod_cast hb.le)
  rcases le_or_gt 1 r with hr1 | hr1
  · rw [log_of_one_le_right _ hr1, Int.ofNat_add_one_out]
exact_mod_cast Nat.lt_of_floor_lt Nat.lt_pow_succ

Depends on / 依赖: Int.ofNat_add_one_out, Nat.clog, Nat.clog_pos, Nat.le_c, Nat.lt_of_floor_lt, Nat.lt_pow_succ_log_self, Nat.one_lt_cast, Nat.succ_le_of_lt, clog_pos, hb.le, hcri.trans_le, hr.trans_lt, hr1.le, le_c, le_or_gt, log_of_one_le_right, log_of_right_le_one, log_of_right_le_zero, lt_of_floor_lt, lt_pow_succ_log_self
-/
theorem lt_zpow_succ_log_self {b : Nat} (hb : 1 < b) (r : R) : r < (b : R) ^ (log b r + 1) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [log_of_right_le_zero _ hr, zero_add, zpow_one]
    exact hr.trans_lt (zero_lt_one.trans_le <| mod_cast hb.le)
  rcases le_or_gt 1 r with hr1 | hr1
  · rw [log_of_one_le_right _ hr1, Int.ofNat_add_one_out]
exact_mod_cast Nat.lt_of_floor_lt Nat.lt_pow_succ_log_self hb _
  · rw [log_of_right_le_one _ hr1.le]
    have hcri : 1 < r⁻¹ := (one_lt_inv₀ hr).2 hr1
    have : 1 <= Nat.clog b ⌈r⁻¹⌉₊ :=
      Nat.succ_le_of_lt (Nat.clog_pos hb <| Nat.one_lt_cast.1 <| hcri.trans_le (Nat.le_ceil _))
    rw [neg_add_eq_sub]; rw [← neg_sub]; rw [← Int.ofNat_one]; rw [← Int.ofNat_sub this]; rw [zpow_neg]; rw [zpow_natCast]; rw [lt_inv_comm₀ hr (pow_pos (Nat.cast_pos.mpr <| zero_lt_one.trans hb) _)]; rw [← Nat.cast_pow]
    refine Nat.lt_ceil.1 ?_
exact Nat.pow_pred_clog_lt_self hb Nat.one_lt_cast.1 hcri.trans_le Nat.le_ceil _

@[simp]
/--
theorem `log_zero_right` / 定理 `log_zero_right`

English:
theorem log_zero_right
  given: (b : Nat)
  statement: log b (0 : R) = 0
  proof: log_of_right_le_zero b le_rfl

@[simp]

中文:
定理 log_zero_right
  条件: (b : 自然数)
  结论: log b (0 : R) = 0
  证明: log_of_right_le_zero b le_rfl

@[simp]

Depends on / 依赖: le_rfl, log_of_right_le_zero
-/
theorem log_zero_right (b : Nat) : log b (0 : R) = 0 :=
  log_of_right_le_zero b le_rfl

@[simp]
/--
theorem `log_one_right` / 定理 `log_one_right`

English:
theorem log_one_right
  given: (b : Nat)
  statement: log b (1 : R) = 0
  proof: by
  rw [log_of_one_le_right _ le_rfl]; rw [Nat.floor_one]; rw [Nat.log_one_right]; rw [Int.ofNat_zero]

omit [IsStrictOrderedRing R] in
@[simp]

中文:
定理 log_one_right
  条件: (b : 自然数)
  结论: log b (1 : R) = 0
  证明: by
  rw [log_of_one_le_right _ le_rfl]; rw [Nat.floor_one]; rw [Nat.log_one_right]; rw [Int.ofNat_zero]

omit [IsStrictOrderedRing R] in
@[simp]

Depends on / 依赖: Int.ofNat_zero, Nat.floor_one, Nat.log_one_right, floor_one, le_rfl, log_of_one_le_right, log_one_right, ofNat_zero
-/
theorem log_one_right (b : Nat) : log b (1 : R) = 0 := by
  rw [log_of_one_le_right _ le_rfl]; rw [Nat.floor_one]; rw [Nat.log_one_right]; rw [Int.ofNat_zero]

omit [IsStrictOrderedRing R] in
@[simp]
/--
theorem `log_zero_left` / 定理 `log_zero_left`

English:
theorem log_zero_left
  given: (r : R)
  statement: log 0 r = 0
  proof: by
  simp only [log, Nat.log_zero_left, Nat.cast_zero, Nat.clog_zero_left, neg_zero, ite_self]

omit [IsStrictOrderedRing R] in
@[simp]

中文:
定理 log_zero_left
  条件: (r : R)
  结论: log 0 r = 0
  证明: by
  simp only [log, Nat.log_zero_left, Nat.cast_zero, Nat.clog_zero_left, neg_zero, ite_self]

omit [IsStrictOrderedRing R] in
@[simp]

Depends on / 依赖: Nat.cast_zero, Nat.clog_zero_left, Nat.log_zero_left, cast_zero, clog_zero_left, ite_self, log_zero_left, neg_zero
-/
theorem log_zero_left (r : R) : log 0 r = 0 := by
  simp only [log, Nat.log_zero_left, Nat.cast_zero, Nat.clog_zero_left, neg_zero, ite_self]

omit [IsStrictOrderedRing R] in
@[simp]
/--
theorem `log_one_left` / 定理 `log_one_left`

English:
theorem log_one_left
  given: (r : R)
  statement: log 1 r = 0
  proof: by
  by_cases hr : 1 <= r
  · simp_all only [log, ↓reduceIte, Nat.log_one_left, Nat.cast_zero]
  · simp only [log, Nat.log_one_left, Nat.cast_zero, Nat.clog_one_left, neg_zero, ite_self]

中文:
定理 log_one_left
  条件: (r : R)
  结论: log 1 r = 0
  证明: by
  by_cases hr : 1 <= r
  · simp_all only [log, ↓reduceIte, Nat.log_one_left, Nat.cast_zero]
  · simp only [log, Nat.log_one_left, Nat.cast_zero, Nat.clog_one_left, neg_zero, ite_self]

Depends on / 依赖: Nat.cast_zero, Nat.clog_one_left, Nat.log_one_left, cast_zero, clog_one_left, ite_self, log_one_left, neg_zero, reduceIte
-/
theorem log_one_left (r : R) : log 1 r = 0 := by
  by_cases hr : 1 <= r
  · simp_all only [log, ↓reduceIte, Nat.log_one_left, Nat.cast_zero]
  · simp only [log, Nat.log_one_left, Nat.cast_zero, Nat.clog_one_left, neg_zero, ite_self]

/--
theorem `log_zpow` / 定理 `log_zpow`

English:
theorem log_zpow
  given: {b : Nat} (hb : 1 < b) (z : Int)
  statement: log b (b ^ z : R) = z
  proof: by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [log_of_one_le_right _ (one_le_zpow₀ (mod_cast hb.le) <| Int.natCast_nonneg _), zpow_natCast,
      ← Nat.cast_pow, Nat.floor_natCast, Nat.log_pow hb]
  · rw [log_of_right_le_one _ (zpow_le_one_of_nonpos₀ (mod_cast hb.le) <|
      neg_nonpos.2

中文:
定理 log_zpow
  条件: {b : 自然数} (hb : 1 < b) (z : 整数)
  结论: log b (b ^ z : R) = z
  证明: by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [log_of_one_le_right _ (one_le_zpow₀ (mod_cast hb.le) <| Int.natCast_nonneg _), zpow_natCast,
      ← Nat.cast_pow, Nat.floor_natCast, Nat.log_pow hb]
  · rw [log_of_right_le_one _ (zpow_le_one_of_nonpos₀ (mod_cast hb.le) <|
      neg_nonpos.2

Depends on / 依赖: Int.eq_nat_or_neg, Int.natCast_nonneg, Nat.cast_pow, Nat.ceil_natCast, Nat.clog_pow, Nat.floor_natCast, Nat.log_pow, cast_pow, ceil_natCast, clog_pow, eq_nat_or_neg, floor_natCast, hb.le, inv_inv, log_of_one_le_right, log_of_right_le_one, log_pow, mod_cast, natCast_nonneg, neg_nonpos
-/
theorem log_zpow {b : Nat} (hb : 1 < b) (z : Int) : log b (b ^ z : R) = z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [log_of_one_le_right _ (one_le_zpow₀ (mod_cast hb.le) <| Int.natCast_nonneg _), zpow_natCast,
      ← Nat.cast_pow, Nat.floor_natCast, Nat.log_pow hb]
  · rw [log_of_right_le_one _ (zpow_le_one_of_nonpos₀ (mod_cast hb.le) <|
      neg_nonpos.2 (Int.natCast_nonneg _)),
      zpow_neg, inv_inv, zpow_natCast, ← Nat.cast_pow, Nat.ceil_natCast, Nat.clog_pow _ _ hb]

@[mono, gcongr]
/--
theorem `log_mono_right` / 定理 `log_mono_right`

English:
theorem log_mono_right
  given: {b : Nat} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ <= r₂)
  statement: log b r₁ <= log b r₂
  proof: by
  rcases le_total r₁ 1 with h₁ | h₁ <;> rcases le_total r₂ 1 with h₂ | h₂
  · have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
    rw [log_of_right_le_one _ h₁]; rw [log_of_right_le_one _ h₂]; rw [neg_le_neg_iff]; rw [Nat.cast_le]
exact Nat.clog_mono_right b Nat.ceil_mono (inv_le_inv₀ h₀' h₀).2 h
  · rw 

中文:
定理 log_mono_right
  条件: {b : 自然数} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ <= r₂)
  结论: log b r₁ <= log b r₂
  证明: by
  rcases le_total r₁ 1 with h₁ | h₁ <;> rcases le_total r₂ 1 with h₂ | h₂
  · have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
    rw [log_of_right_le_one _ h₁]; rw [log_of_right_le_one _ h₂]; rw [neg_le_neg_iff]; rw [Nat.cast_le]
exact Nat.clog_mono_right b Nat.ceil_mono (inv_le_inv₀ h₀' h₀).2 h
  · rw 

Depends on / 依赖: Int.natCast_nonneg, Nat.cast_le, Nat.ceil_mono, Nat.clog_mono_right, cast_le, ceil_mono, clog_mono_right, le_antisymm, le_total, log_of_one_le_right, log_of_right_le_one, lt_of_lt_of_le, natCast_nonneg, neg_le_neg_iff, neg_nonpos, neg_nonpos.mpr
-/
theorem log_mono_right {b : Nat} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ <= r₂) : log b r₁ <= log b r₂ := by
  rcases le_total r₁ 1 with h₁ | h₁ <;> rcases le_total r₂ 1 with h₂ | h₂
  · have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
    rw [log_of_right_le_one _ h₁]; rw [log_of_right_le_one _ h₂]; rw [neg_le_neg_iff]; rw [Nat.cast_le]
exact Nat.clog_mono_right b Nat.ceil_mono (inv_le_inv₀ h₀' h₀).2 h
  · rw [log_of_right_le_one _ h₁, log_of_one_le_right _ h₂]
    exact (neg_nonpos.mpr (Int.natCast_nonneg _)).trans (Int.natCast_nonneg _)
  · obtain rfl := le_antisymm h (h₂.trans h₁)
    rfl
  · rw [log_of_one_le_right _ h₁, log_of_one_le_right _ h₂, Nat.cast_le]
    exact Nat.log_mono_right (Nat.floor_mono h)

variable (R) in
/--
Definition of `zpowLogGi` / `zpowLogGi` 的定义

English:
definition zpowLogGi
  signature: {b : Nat} (hb : 1 < b)
  body: GaloisCoinsertion.monotoneIntro (fun r₁ _ => log_mono_right r₁.2)
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r => Subtype.coe_le_coe.mp <| zpow_log_le_self hb r.2) fun _ => log_zpow (R := R) hb _

中文:
定义 zpowLogGi
  签名: {b : 自然数} (hb : 1 < b)
  定义体: GaloisCoinsertion.monotoneIntro (fun r₁ _ => log_mono_right r₁.2)
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r => Subtype.coe_le_coe.mp <| zpow_log_le_self hb r.2) fun _ => log_zpow (R := R) hb _

Depends on / 依赖: GaloisCoinsertion, GaloisCoinsertion.monotoneIntro, Subtype, Subtype.coe_le_coe.mp, coe_le_coe, log_mono_right, log_zpow, mod_cast, monotone, monotoneIntro, zpow_log_le_self
-/
def zpowLogGi {b : Nat} (hb : 1 < b) :
    GaloisCoinsertion
      (fun z : Int =>
Subtype.mk ((b : R) ^ z) zpow_pos (mod_cast zero_lt_one.trans hb) z)
      fun r : Set.Ioi (0 : R) => Int.log b (r : R) :=
  GaloisCoinsertion.monotoneIntro (fun r₁ _ => log_mono_right r₁.2)
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r => Subtype.coe_le_coe.mp <| zpow_log_le_self hb r.2) fun _ => log_zpow (R := R) hb _

/--
theorem `lt_zpow_iff_log_lt` / 定理 `lt_zpow_iff_log_lt`

English:
theorem lt_zpow_iff_log_lt
  given: {b : Nat} (hb : 1 < b) {x : Int} {r : R} (hr : 0 < r)
  proof: @GaloisConnection.lt_iff_lt _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

中文:
定理 lt_zpow_iff_log_lt
  条件: {b : 自然数} (hb : 1 < b) {x : 整数} {r : R} (hr : 0 < r)
  证明: @GaloisConnection.lt_iff_lt _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

Depends on / 依赖: GaloisConnection, GaloisConnection.lt_iff_lt, lt_iff_lt, zpowLogGi
-/
theorem lt_zpow_iff_log_lt {b : Nat} (hb : 1 < b) {x : Int} {r : R} (hr : 0 < r) :
    r < (b : R) ^ x ↔ log b r < x :=
  @GaloisConnection.lt_iff_lt _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

/--
theorem `zpow_le_iff_le_log` / 定理 `zpow_le_iff_le_log`

English:
theorem zpow_le_iff_le_log
  given: {b : Nat} (hb : 1 < b) {x : Int} {r : R} (hr : 0 < r)
  proof: @GaloisConnection.le_iff_le _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

中文:
定理 zpow_le_iff_le_log
  条件: {b : 自然数} (hb : 1 < b) {x : 整数} {r : R} (hr : 0 < r)
  证明: @GaloisConnection.le_iff_le _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

Depends on / 依赖: GaloisConnection, GaloisConnection.le_iff_le, le_iff_le, zpowLogGi
-/
theorem zpow_le_iff_le_log {b : Nat} (hb : 1 < b) {x : Int} {r : R} (hr : 0 < r) :
    (b : R) ^ x <= r ↔ x <= log b r :=
  @GaloisConnection.le_iff_le _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

/--
Definition of `clog` / `clog` 的定义

English:
definition clog
  signature: (b : Nat) (r : R)
  body: if 1 <= r then Nat.clog b ⌈r⌉₊ else -Nat.log b ⌊r⁻¹⌋₊

omit [IsStrictOrderedRing R] in

中文:
定义 clog
  签名: (b : 自然数) (r : R)
  定义体: if 1 <= r then Nat.clog b ⌈r⌉₊ else -Nat.log b ⌊r⁻¹⌋₊

omit [IsStrictOrderedRing R] in

Depends on / 依赖: Nat.clog, Nat.log
-/
def clog (b : Nat) (r : R) : Int :=
  if 1 <= r then Nat.clog b ⌈r⌉₊ else -Nat.log b ⌊r⁻¹⌋₊

omit [IsStrictOrderedRing R] in
/--
theorem `clog_of_one_le_right` / 定理 `clog_of_one_le_right`

English:
theorem clog_of_one_le_right
  given: (b : Nat) {r : R} (hr : 1 <= r)
  statement: clog b r = Nat.clog b ⌈r⌉₊
  proof: if_pos hr

中文:
定理 clog_of_one_le_right
  条件: (b : 自然数) {r : R} (hr : 1 <= r)
  结论: clog b r = 自然数.clog b ⌈r⌉₊
  证明: if_pos hr

Depends on / 依赖: if_pos
-/
theorem clog_of_one_le_right (b : Nat) {r : R} (hr : 1 <= r) : clog b r = Nat.clog b ⌈r⌉₊ :=
  if_pos hr

/--
theorem `clog_of_right_le_one` / 定理 `clog_of_right_le_one`

English:
theorem clog_of_right_le_one
  given: (b : Nat) {r : R} (hr : r <= 1)
  statement: clog b r = -Nat.log b ⌊r⁻¹⌋₊
  proof: by
  obtain rfl | hr := hr.eq_or_lt
  · rw [clog, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right,
      Nat.clog_one_right, Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_ge

中文:
定理 clog_of_right_le_one
  条件: (b : 自然数) {r : R} (hr : r <= 1)
  结论: clog b r = -自然数.log b ⌊r⁻¹⌋₊
  证明: by
  obtain rfl | hr := hr.eq_or_lt
  · rw [clog, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right,
      Nat.clog_one_right, Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_ge

Depends on / 依赖: Int.ofNat_zero, Nat.ceil_one, Nat.clog_one_right, Nat.floor_one, Nat.log_one_right, ceil_one, clog_one_right, eq_or_lt, floor_one, hr.eq_or_lt, hr.not_ge, if_neg, if_pos, inv_one, log_one_right, neg_zero, not_ge, ofNat_zero
-/
theorem clog_of_right_le_one (b : Nat) {r : R} (hr : r <= 1) : clog b r = -Nat.log b ⌊r⁻¹⌋₊ := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [clog, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right,
      Nat.clog_one_right, Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_ge

/--
theorem `clog_of_right_le_zero` / 定理 `clog_of_right_le_zero`

English:
theorem clog_of_right_le_zero
  given: (b : Nat) {r : R} (hr : r <= 0)
  statement: clog b r = 0
  proof: by
  rw [clog]; rw [if_neg (hr.trans_lt zero_lt_one).not_ge]; rw [neg_eq_zero]; rw [Int.natCast_eq_zero]; rw [Nat.log_eq_zero_iff]
  rcases le_or_gt b 1 with hb | hb
  · exact Or.inr hb
  · refine Or.inl (lt_of_le_of_lt ?_ hb)
    exact Nat.floor_le_one_of_le_one ((inv_nonpos.2 hr).trans zero_le_one

中文:
定理 clog_of_right_le_zero
  条件: (b : 自然数) {r : R} (hr : r <= 0)
  结论: clog b r = 0
  证明: by
  rw [clog]; rw [if_neg (hr.trans_lt zero_lt_one).not_ge]; rw [neg_eq_zero]; rw [Int.natCast_eq_zero]; rw [Nat.log_eq_zero_iff]
  rcases le_or_gt b 1 with hb | hb
  · exact Or.inr hb
  · refine Or.inl (lt_of_le_of_lt ?_ hb)
    exact Nat.floor_le_one_of_le_one ((inv_nonpos.2 hr).trans zero_le_one

Depends on / 依赖: Int.natCast_eq_zero, Nat.floor_le_one_of_le_one, Nat.log_eq_zero_iff, Or.inl, Or.inr, floor_le_one_of_le_one, hr.trans_lt, if_neg, inv_nonpos, le_or_gt, log_eq_zero_iff, lt_of_le_of_lt, natCast_eq_zero, neg_eq_zero, not_ge, trans_lt, zero_le_one, zero_lt_one
-/
theorem clog_of_right_le_zero (b : Nat) {r : R} (hr : r <= 0) : clog b r = 0 := by
  rw [clog]; rw [if_neg (hr.trans_lt zero_lt_one).not_ge]; rw [neg_eq_zero]; rw [Int.natCast_eq_zero]; rw [Nat.log_eq_zero_iff]
  rcases le_or_gt b 1 with hb | hb
  · exact Or.inr hb
  · refine Or.inl (lt_of_le_of_lt ?_ hb)
    exact Nat.floor_le_one_of_le_one ((inv_nonpos.2 hr).trans zero_le_one)

@[simp]
/--
theorem `clog_inv` / 定理 `clog_inv`

English:
theorem clog_inv
  given: (b : Nat) (r : R)
  statement: clog b r⁻¹ = -log b r
  proof: by
  rcases lt_or_ge 0 r with hrp | hrp
  · obtain hr | hr := le_total 1 r
    · rw [clog_of_right_le_one _ (inv_le_one_of_one_le₀ hr), log_of_one_le_right _ hr, inv_inv]
    · rw [clog_of_one_le_right _ ((one_le_inv₀ hrp).2 hr), log_of_right_le_one _ hr, neg_neg]
  · rw [clog_of_right_le_zero _ (in

中文:
定理 clog_inv
  条件: (b : 自然数) (r : R)
  结论: clog b r⁻¹ = -log b r
  证明: by
  rcases lt_or_ge 0 r with hrp | hrp
  · obtain hr | hr := le_total 1 r
    · rw [clog_of_right_le_one _ (inv_le_one_of_one_le₀ hr), log_of_one_le_right _ hr, inv_inv]
    · rw [clog_of_one_le_right _ ((one_le_inv₀ hrp).2 hr), log_of_right_le_one _ hr, neg_neg]
  · rw [clog_of_right_le_zero _ (in

Depends on / 依赖: clog_of_one_le_right, clog_of_right_le_one, clog_of_right_le_zero, inv_inv, inv_nonpos, inv_nonpos.mpr, le_total, log_of_one_le_right, log_of_right_le_one, log_of_right_le_zero, lt_or_ge, neg_neg, neg_zero
-/
theorem clog_inv (b : Nat) (r : R) : clog b r⁻¹ = -log b r := by
  rcases lt_or_ge 0 r with hrp | hrp
  · obtain hr | hr := le_total 1 r
    · rw [clog_of_right_le_one _ (inv_le_one_of_one_le₀ hr), log_of_one_le_right _ hr, inv_inv]
    · rw [clog_of_one_le_right _ ((one_le_inv₀ hrp).2 hr), log_of_right_le_one _ hr, neg_neg]
  · rw [clog_of_right_le_zero _ (inv_nonpos.mpr hrp), log_of_right_le_zero _ hrp, neg_zero]

@[simp]
/--
theorem `log_inv` / 定理 `log_inv`

English:
theorem log_inv
  given: (b : Nat) (r : R)
  statement: log b r⁻¹ = -clog b r
  proof: by
  rw [← inv_inv r]; rw [clog_inv]; rw [neg_neg]; rw [inv_inv]

中文:
定理 log_inv
  条件: (b : 自然数) (r : R)
  结论: log b r⁻¹ = -clog b r
  证明: by
  rw [← inv_inv r]; rw [clog_inv]; rw [neg_neg]; rw [inv_inv]

Depends on / 依赖: clog_inv, inv_inv, neg_neg
-/
theorem log_inv (b : Nat) (r : R) : log b r⁻¹ = -clog b r := by
  rw [← inv_inv r]; rw [clog_inv]; rw [neg_neg]; rw [inv_inv]

-- note this is useful for writing in reverse
/--
theorem `neg_log_inv_eq_clog` / 定理 `neg_log_inv_eq_clog`

English:
theorem neg_log_inv_eq_clog
  given: (b : Nat) (r : R)
  statement: -log b r⁻¹ = clog b r
  proof: by rw [log_inv, neg_neg]

中文:
定理 neg_log_inv_eq_clog
  条件: (b : 自然数) (r : R)
  结论: -log b r⁻¹ = clog b r
  证明: by rw [log_inv, neg_neg]

Depends on / 依赖: log_inv, neg_neg
-/
theorem neg_log_inv_eq_clog (b : Nat) (r : R) : -log b r⁻¹ = clog b r := by rw [log_inv, neg_neg]

/--
theorem `neg_clog_inv_eq_log` / 定理 `neg_clog_inv_eq_log`

English:
theorem neg_clog_inv_eq_log
  given: (b : Nat) (r : R)
  statement: -clog b r⁻¹ = log b r
  proof: by rw [clog_inv, neg_neg]

@[simp, norm_cast]

中文:
定理 neg_clog_inv_eq_log
  条件: (b : 自然数) (r : R)
  结论: -clog b r⁻¹ = log b r
  证明: by rw [clog_inv, neg_neg]

@[simp, norm_cast]

Depends on / 依赖: clog_inv, neg_neg
-/
theorem neg_clog_inv_eq_log (b : Nat) (r : R) : -clog b r⁻¹ = log b r := by rw [clog_inv, neg_neg]

@[simp, norm_cast]
/--
theorem `clog_natCast` / 定理 `clog_natCast`

English:
theorem clog_natCast
  given: (b : Nat) (n : Nat)
  statement: clog b (n : R) = Nat.clog b n
  proof: by
  rcases n with - | n
  · simp [clog_of_right_le_one]
  · rw [clog_of_one_le_right, (Nat.ceil_eq_iff (Nat.succ_ne_zero n)).mpr] <;> simp

@[simp]

中文:
定理 clog_natCast
  条件: (b : 自然数) (n : 自然数)
  结论: clog b (n : R) = 自然数.clog b n
  证明: by
  rcases n with - | n
  · simp [clog_of_right_le_one]
  · rw [clog_of_one_le_right, (Nat.ceil_eq_iff (Nat.succ_ne_zero n)).mpr] <;> simp

@[simp]

Depends on / 依赖: Nat.ceil_eq_iff, Nat.succ_ne_zero, ceil_eq_iff, clog_of_one_le_right, clog_of_right_le_one, succ_ne_zero
-/
theorem clog_natCast (b : Nat) (n : Nat) : clog b (n : R) = Nat.clog b n := by
  rcases n with - | n
  · simp [clog_of_right_le_one]
  · rw [clog_of_one_le_right, (Nat.ceil_eq_iff (Nat.succ_ne_zero n)).mpr] <;> simp

@[simp]
/--
theorem `clog_ofNat` / 定理 `clog_ofNat`

English:
theorem clog_ofNat
  given: (b : Nat) (n : Nat) [n.AtLeastTwo]
  proof: clog_natCast b n

中文:
定理 clog_of自然数
  条件: (b : 自然数) (n : 自然数) [n.AtLeastTwo]
  证明: clog_natCast b n

Depends on / 依赖: clog_natCast
-/
theorem clog_ofNat (b : Nat) (n : Nat) [n.AtLeastTwo] :
    clog b (ofNat(n) : R) = Nat.clog b ofNat(n) :=
  clog_natCast b n

/--
theorem `clog_of_left_le_one` / 定理 `clog_of_left_le_one`

English:
theorem clog_of_left_le_one
  given: {b : Nat} (hb : b <= 1) (r : R)
  statement: clog b r = 0
  proof: by
  rw [← neg_log_inv_eq_clog]; rw [log_of_left_le_one hb]; rw [neg_zero]

中文:
定理 clog_of_left_le_one
  条件: {b : 自然数} (hb : b <= 1) (r : R)
  结论: clog b r = 0
  证明: by
  rw [← neg_log_inv_eq_clog]; rw [log_of_left_le_one hb]; rw [neg_zero]

Depends on / 依赖: log_of_left_le_one, neg_log_inv_eq_clog, neg_zero
-/
theorem clog_of_left_le_one {b : Nat} (hb : b <= 1) (r : R) : clog b r = 0 := by
  rw [← neg_log_inv_eq_clog]; rw [log_of_left_le_one hb]; rw [neg_zero]

/--
theorem `self_le_zpow_clog` / 定理 `self_le_zpow_clog`

English:
theorem self_le_zpow_clog
  given: {b : Nat} (hb : 1 < b) (r : R)
  statement: r <= (b : R) ^ clog b r
  proof: by
  rcases le_or_gt r 0 with hr | hr
  · rw [clog_of_right_le_zero _ hr, zpow_zero]
    exact hr.trans zero_le_one
  rw [← neg_log_inv_eq_clog]; rw [zpow_neg]; rw [le_inv_comm₀ hr (zpow_pos ..)]
  · exact zpow_log_le_self hb (inv_pos.mpr hr)
  · exact Nat.cast_pos.mpr (zero_le_one.trans_lt hb)

中文:
定理 self_le_zpow_clog
  条件: {b : 自然数} (hb : 1 < b) (r : R)
  结论: r <= (b : R) ^ clog b r
  证明: by
  rcases le_or_gt r 0 with hr | hr
  · rw [clog_of_right_le_zero _ hr, zpow_zero]
    exact hr.trans zero_le_one
  rw [← neg_log_inv_eq_clog]; rw [zpow_neg]; rw [le_inv_comm₀ hr (zpow_pos ..)]
  · exact zpow_log_le_self hb (inv_pos.mpr hr)
  · exact Nat.cast_pos.mpr (zero_le_one.trans_lt hb)

Depends on / 依赖: Nat.cast_pos.mpr, cast_pos, clog_of_right_le_zero, hr.trans, inv_pos, inv_pos.mpr, le_or_gt, neg_log_inv_eq_clog, trans_lt, zero_le_one, zero_le_one.trans_lt, zpow_log_le_self, zpow_neg, zpow_pos, zpow_zero
-/
theorem self_le_zpow_clog {b : Nat} (hb : 1 < b) (r : R) : r <= (b : R) ^ clog b r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [clog_of_right_le_zero _ hr, zpow_zero]
    exact hr.trans zero_le_one
  rw [← neg_log_inv_eq_clog]; rw [zpow_neg]; rw [le_inv_comm₀ hr (zpow_pos ..)]
  · exact zpow_log_le_self hb (inv_pos.mpr hr)
  · exact Nat.cast_pos.mpr (zero_le_one.trans_lt hb)

/--
theorem `zpow_pred_clog_lt_self` / 定理 `zpow_pred_clog_lt_self`

English:
theorem zpow_pred_clog_lt_self
  given: {b : Nat} {r : R} (hb : 1 < b) (hr : 0 < r)
  proof: by
  rw [← neg_log_inv_eq_clog]; rw [← neg_add']; rw [zpow_neg]; rw [inv_lt_comm₀ _ hr]
  · exact lt_zpow_succ_log_self hb _
  · exact zpow_pos (Nat.cast_pos.mpr <| zero_le_one.trans_lt hb) _

@[simp]

中文:
定理 zpow_pred_clog_lt_self
  条件: {b : 自然数} {r : R} (hb : 1 < b) (hr : 0 < r)
  证明: by
  rw [← neg_log_inv_eq_clog]; rw [← neg_add']; rw [zpow_neg]; rw [inv_lt_comm₀ _ hr]
  · exact lt_zpow_succ_log_self hb _
  · exact zpow_pos (Nat.cast_pos.mpr <| zero_le_one.trans_lt hb) _

@[simp]

Depends on / 依赖: Nat.cast_pos.mpr, cast_pos, lt_zpow_succ_log_self, neg_add, neg_log_inv_eq_clog, trans_lt, zero_le_one, zero_le_one.trans_lt, zpow_neg, zpow_pos
-/
theorem zpow_pred_clog_lt_self {b : Nat} {r : R} (hb : 1 < b) (hr : 0 < r) :
    (b : R) ^ (clog b r - 1) < r := by
  rw [← neg_log_inv_eq_clog]; rw [← neg_add']; rw [zpow_neg]; rw [inv_lt_comm₀ _ hr]
  · exact lt_zpow_succ_log_self hb _
  · exact zpow_pos (Nat.cast_pos.mpr <| zero_le_one.trans_lt hb) _

@[simp]
/--
theorem `clog_zero_right` / 定理 `clog_zero_right`

English:
theorem clog_zero_right
  given: (b : Nat)
  statement: clog b (0 : R) = 0
  proof: clog_of_right_le_zero _ le_rfl

@[simp]

中文:
定理 clog_zero_right
  条件: (b : 自然数)
  结论: clog b (0 : R) = 0
  证明: clog_of_right_le_zero _ le_rfl

@[simp]

Depends on / 依赖: clog_of_right_le_zero, le_rfl
-/
theorem clog_zero_right (b : Nat) : clog b (0 : R) = 0 :=
  clog_of_right_le_zero _ le_rfl

@[simp]
/--
theorem `clog_one_right` / 定理 `clog_one_right`

English:
theorem clog_one_right
  given: (b : Nat)
  statement: clog b (1 : R) = 0
  proof: by
  rw [clog_of_one_le_right _ le_rfl]; rw [Nat.ceil_one]; rw [Nat.clog_one_right]; rw [Int.ofNat_zero]

omit [IsStrictOrderedRing R] in
@[simp]

中文:
定理 clog_one_right
  条件: (b : 自然数)
  结论: clog b (1 : R) = 0
  证明: by
  rw [clog_of_one_le_right _ le_rfl]; rw [Nat.ceil_one]; rw [Nat.clog_one_right]; rw [Int.ofNat_zero]

omit [IsStrictOrderedRing R] in
@[simp]

Depends on / 依赖: Int.ofNat_zero, Nat.ceil_one, Nat.clog_one_right, ceil_one, clog_of_one_le_right, clog_one_right, le_rfl, ofNat_zero
-/
theorem clog_one_right (b : Nat) : clog b (1 : R) = 0 := by
  rw [clog_of_one_le_right _ le_rfl]; rw [Nat.ceil_one]; rw [Nat.clog_one_right]; rw [Int.ofNat_zero]

omit [IsStrictOrderedRing R] in
@[simp]
/--
theorem `clog_zero_left` / 定理 `clog_zero_left`

English:
theorem clog_zero_left
  given: (r : R)
  statement: clog 0 r = 0
  proof: by
  by_cases hr : 1 <= r
  · simp only [clog, Nat.clog_zero_left, Nat.cast_zero, Nat.log_zero_left, neg_zero, ite_self]
  · simp only [clog, hr, ite_cond_eq_false, Nat.log_zero_left, Nat.cast_zero, neg_zero]

omit [IsStrictOrderedRing R] in
@[simp]

中文:
定理 clog_zero_left
  条件: (r : R)
  结论: clog 0 r = 0
  证明: by
  by_cases hr : 1 <= r
  · simp only [clog, Nat.clog_zero_left, Nat.cast_zero, Nat.log_zero_left, neg_zero, ite_self]
  · simp only [clog, hr, ite_cond_eq_false, Nat.log_zero_left, Nat.cast_zero, neg_zero]

omit [IsStrictOrderedRing R] in
@[simp]

Depends on / 依赖: Nat.cast_zero, Nat.clog_zero_left, Nat.log_zero_left, cast_zero, clog_zero_left, ite_cond_eq_false, ite_self, log_zero_left, neg_zero
-/
theorem clog_zero_left (r : R) : clog 0 r = 0 := by
  by_cases hr : 1 <= r
  · simp only [clog, Nat.clog_zero_left, Nat.cast_zero, Nat.log_zero_left, neg_zero, ite_self]
  · simp only [clog, hr, ite_cond_eq_false, Nat.log_zero_left, Nat.cast_zero, neg_zero]

omit [IsStrictOrderedRing R] in
@[simp]
/--
theorem `clog_one_left` / 定理 `clog_one_left`

English:
theorem clog_one_left
  given: (r : R)
  statement: clog 1 r = 0
  proof: by
  simp only [clog, Nat.log_one_left, Nat.cast_zero, Nat.clog_one_left, neg_zero, ite_self]

中文:
定理 clog_one_left
  条件: (r : R)
  结论: clog 1 r = 0
  证明: by
  simp only [clog, Nat.log_one_left, Nat.cast_zero, Nat.clog_one_left, neg_zero, ite_self]

Depends on / 依赖: Nat.cast_zero, Nat.clog_one_left, Nat.log_one_left, cast_zero, clog_one_left, ite_self, log_one_left, neg_zero
-/
theorem clog_one_left (r : R) : clog 1 r = 0 := by
  simp only [clog, Nat.log_one_left, Nat.cast_zero, Nat.clog_one_left, neg_zero, ite_self]

/--
theorem `clog_zpow` / 定理 `clog_zpow`

English:
theorem clog_zpow
  given: {b : Nat} (hb : 1 < b) (z : Int)
  statement: clog b (b ^ z : R) = z
  proof: by
  rw [← neg_log_inv_eq_clog]; rw [← zpow_neg]; rw [log_zpow hb]; rw [neg_neg]

@[gcongr, mono]

中文:
定理 clog_zpow
  条件: {b : 自然数} (hb : 1 < b) (z : 整数)
  结论: clog b (b ^ z : R) = z
  证明: by
  rw [← neg_log_inv_eq_clog]; rw [← zpow_neg]; rw [log_zpow hb]; rw [neg_neg]

@[gcongr, mono]

Depends on / 依赖: log_zpow, neg_log_inv_eq_clog, neg_neg, zpow_neg
-/
theorem clog_zpow {b : Nat} (hb : 1 < b) (z : Int) : clog b (b ^ z : R) = z := by
  rw [← neg_log_inv_eq_clog]; rw [← zpow_neg]; rw [log_zpow hb]; rw [neg_neg]

@[gcongr, mono]
/--
theorem `clog_mono_right` / 定理 `clog_mono_right`

English:
theorem clog_mono_right
  given: {b : Nat} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ <= r₂)
  proof: by
  have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
  rw [← neg_log_inv_eq_clog]; rw [← neg_log_inv_eq_clog]; rw [neg_le_neg_iff]
exact log_mono_right (inv_pos_of_pos h₀') (inv_le_inv₀ h₀' h₀).2 h

中文:
定理 clog_mono_right
  条件: {b : 自然数} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ <= r₂)
  证明: by
  have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
  rw [← neg_log_inv_eq_clog]; rw [← neg_log_inv_eq_clog]; rw [neg_le_neg_iff]
exact log_mono_right (inv_pos_of_pos h₀') (inv_le_inv₀ h₀' h₀).2 h

Depends on / 依赖: inv_pos_of_pos, log_mono_right, lt_of_lt_of_le, neg_le_neg_iff, neg_log_inv_eq_clog
-/
theorem clog_mono_right {b : Nat} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ <= r₂) :
    clog b r₁ <= clog b r₂ := by
  have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
  rw [← neg_log_inv_eq_clog]; rw [← neg_log_inv_eq_clog]; rw [neg_le_neg_iff]
exact log_mono_right (inv_pos_of_pos h₀') (inv_le_inv₀ h₀' h₀).2 h

variable (R) in
/--
Definition of `clogZPowGi` / `clogZPowGi` 的定义

English:
definition clogZPowGi
  signature: {b : Nat} (hb : 1 < b)
  body: GaloisInsertion.monotoneIntro
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r₁ _ => clog_mono_right r₁.2)
    (fun _ => Subtype.coe_le_coe.mp <| self_le_zpow_clog hb _) fun _ => clog_zpow (R := R) hb _

中文:
定义 clogZPowGi
  签名: {b : 自然数} (hb : 1 < b)
  定义体: GaloisInsertion.monotoneIntro
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r₁ _ => clog_mono_right r₁.2)
    (fun _ => Subtype.coe_le_coe.mp <| self_le_zpow_clog hb _) fun _ => clog_zpow (R := R) hb _

Depends on / 依赖: GaloisInsertion, GaloisInsertion.monotoneIntro, Subtype, Subtype.coe_le_coe.mp, clog_mono_right, clog_zpow, coe_le_coe, mod_cast, monotone, monotoneIntro, self_le_zpow_clog
-/
def clogZPowGi {b : Nat} (hb : 1 < b) :
    GaloisInsertion (fun r : Set.Ioi (0 : R) => Int.clog b (r : R)) fun z : Int =>
      ⟨(b : R) ^ z, zpow_pos (mod_cast zero_lt_one.trans hb) z⟩ :=
  GaloisInsertion.monotoneIntro
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r₁ _ => clog_mono_right r₁.2)
    (fun _ => Subtype.coe_le_coe.mp <| self_le_zpow_clog hb _) fun _ => clog_zpow (R := R) hb _

/--
theorem `zpow_lt_iff_lt_clog` / 定理 `zpow_lt_iff_lt_clog`

English:
theorem zpow_lt_iff_lt_clog
  given: {b : Nat} (hb : 1 < b) {x : Int} {r : R} (hr : 0 < r)
  proof: (@GaloisConnection.lt_iff_lt _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

中文:
定理 zpow_lt_iff_lt_clog
  条件: {b : 自然数} (hb : 1 < b) {x : 整数} {r : R} (hr : 0 < r)
  证明: (@GaloisConnection.lt_iff_lt _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

Depends on / 依赖: GaloisConnection, GaloisConnection.lt_iff_lt, clogZPowGi, lt_iff_lt
-/
theorem zpow_lt_iff_lt_clog {b : Nat} (hb : 1 < b) {x : Int} {r : R} (hr : 0 < r) :
    (b : R) ^ x < r ↔ x < clog b r :=
  (@GaloisConnection.lt_iff_lt _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

/--
theorem `le_zpow_iff_clog_le` / 定理 `le_zpow_iff_clog_le`

English:
theorem le_zpow_iff_clog_le
  given: {b : Nat} (hb : 1 < b) {x : Int} {r : R} (hr : 0 < r)
  proof: (@GaloisConnection.le_iff_le _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

中文:
定理 le_zpow_iff_clog_le
  条件: {b : 自然数} (hb : 1 < b) {x : 整数} {r : R} (hr : 0 < r)
  证明: (@GaloisConnection.le_iff_le _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

Depends on / 依赖: GaloisConnection, GaloisConnection.le_iff_le, clogZPowGi, le_iff_le
-/
theorem le_zpow_iff_clog_le {b : Nat} (hb : 1 < b) {x : Int} {r : R} (hr : 0 < r) :
    r <= (b : R) ^ x ↔ clog b r <= x :=
  (@GaloisConnection.le_iff_le _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

end Int
