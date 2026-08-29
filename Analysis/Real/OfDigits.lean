/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Qify

/-!
# Representation of reals in positional system

This file defines `Real.ofDigits` and `Real.digits` functions which allows to work with the
representations of reals as sequences of digits in positional system.

## Main Definitions

* `ofDigits`: takes a sequence of digits `(d₀, d₁, ...)` (as an `ℕ → Fin b`),
  and returns the real number `0.d₀d₁d₂...`.
* `digits`: takes a real number in $[0,1)$ and returns the sequence of its digits.

## Main Statements

* `ofDigits_digits` states that `ofDigits (digits x b) = x`.
-/

@[expose] public section

namespace Real

/--
Definition of `ofDigitsTerm` / `ofDigitsTerm` 的定义

English:
definition ofDigitsTerm
  signature: {b : Nat} (digits : Nat -> Fin b)
  body: fun i => (digits i) * ((b : Real) ^ (i + 1))⁻¹

中文:
定义 ofDigitsTerm
  签名: {b : 自然数} (digits : 自然数 -> 有限集 b)
  定义体: fun i => (digits i) * ((b : Real) ^ (i + 1))⁻¹

Depends on / 依赖: digits
-/
noncomputable def ofDigitsTerm {b : Nat} (digits : Nat -> Fin b) : Nat -> Real :=
  fun i => (digits i) * ((b : Real) ^ (i + 1))⁻¹

/--
theorem `ofDigitsTerm_nonneg` / 定理 `ofDigitsTerm_nonneg`

English:
theorem ofDigitsTerm_nonneg
  given: {b : Nat} {digits : Nat -> Fin b} {n : Nat}
  proof: by
  simp only [ofDigitsTerm]
  positivity

中文:
定理 ofDigitsTerm_nonneg
  条件: {b : 自然数} {digits : 自然数 -> 有限集 b} {n : 自然数}
  证明: by
  simp only [ofDigitsTerm]
  positivity

Depends on / 依赖: ofDigitsTerm
-/
theorem ofDigitsTerm_nonneg {b : Nat} {digits : Nat -> Fin b} {n : Nat} :
    0 <= ofDigitsTerm digits n := by
  simp only [ofDigitsTerm]
  positivity

/--
lemma `b_pos` / 引理 `b_pos`

English:
lemma b_pos
  given: {b : Nat} (digits : Nat -> Fin b)
  statement: 0 < b
  proof: Fin.pos (digits 0)

中文:
引理 b_pos
  条件: {b : 自然数} (digits : 自然数 -> 有限集 b)
  结论: 0 < b
  证明: Fin.pos (digits 0)
-/
private lemma b_pos {b : Nat} (digits : Nat -> Fin b) : 0 < b := Fin.pos (digits 0)

/--
theorem `ofDigitsTerm_le` / 定理 `ofDigitsTerm_le`

English:
theorem ofDigitsTerm_le
  given: {b : Nat} {digits : Nat -> Fin b} {n : Nat}
  proof: by
  obtain ⟨c, rfl⟩ := Nat.exists_add_one_eq.mpr (b_pos digits)
  unfold ofDigitsTerm
  gcongr
  simp
  grind

中文:
定理 ofDigitsTerm_le
  条件: {b : 自然数} {digits : 自然数 -> 有限集 b} {n : 自然数}
  证明: by
  obtain ⟨c, rfl⟩ := Nat.exists_add_one_eq.mpr (b_pos digits)
  unfold ofDigitsTerm
  gcongr
  simp
  grind

Depends on / 依赖: Nat.exists_add_one_eq.mpr, b_pos, digits, exists_add_one_eq, ofDigitsTerm
-/
theorem ofDigitsTerm_le {b : Nat} {digits : Nat -> Fin b} {n : Nat} :
    ofDigitsTerm digits n <= (b - 1) * ((b : Real) ^ (n + 1))⁻¹ := by
  obtain ⟨c, rfl⟩ := Nat.exists_add_one_eq.mpr (b_pos digits)
  unfold ofDigitsTerm
  gcongr
  simp
  grind

/--
theorem `summable_ofDigitsTerm` / 定理 `summable_ofDigitsTerm`

English:
theorem summable_ofDigitsTerm
  given: {b : Nat} {digits : Nat -> Fin b}
  proof: by
  refine Summable.of_nonneg_of_le (fun _ => ofDigitsTerm_nonneg) (fun _ => ofDigitsTerm_le) ?_
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simp
  simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
  refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity)

中文:
定理 summable_ofDigitsTerm
  条件: {b : 自然数} {digits : 自然数 -> 有限集 b}
  证明: by
  refine Summable.of_nonneg_of_le (fun _ => ofDigitsTerm_nonneg) (fun _ => ofDigitsTerm_le) ?_
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simp
  simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
  refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity)

Depends on / 依赖: Nat.one_le_of_lt, Summable, Summable.mul_left, Summable.of_nonneg_of_le, b_pos, digits, eq_or_lt, inv_pow, mul_assoc, mul_inv, mul_left, ofDigitsTerm_le, ofDigitsTerm_nonneg, of_nonneg_of_le, one_le_of_lt, pow_succ, simp_rw, summable_geometric_of_lt_one
-/
theorem summable_ofDigitsTerm {b : Nat} {digits : Nat -> Fin b} :
    Summable (ofDigitsTerm digits) := by
  refine Summable.of_nonneg_of_le (fun _ => ofDigitsTerm_nonneg) (fun _ => ofDigitsTerm_le) ?_
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simp
  simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
  refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
  simp [inv_lt_one_iff₀, hb]

/--
Definition of `ofDigits` / `ofDigits` 的定义

English:
definition ofDigits
  signature: {b : Nat} (digits : Nat -> Fin b)
  body: ∑' n, ofDigitsTerm digits n

中文:
定义 ofDigits
  签名: {b : 自然数} (digits : 自然数 -> 有限集 b)
  定义体: ∑' n, ofDigitsTerm digits n

Depends on / 依赖: digits, ofDigitsTerm
-/
noncomputable def ofDigits {b : Nat} (digits : Nat -> Fin b) : Real :=
  ∑' n, ofDigitsTerm digits n

/--
theorem `ofDigits_nonneg` / 定理 `ofDigits_nonneg`

English:
theorem ofDigits_nonneg
  given: {b : Nat} (digits : Nat -> Fin b)
  statement: 0 <= ofDigits digits
  proof: by
  simp only [ofDigits]
  exact tsum_nonneg fun _ => ofDigitsTerm_nonneg

中文:
定理 ofDigits_nonneg
  条件: {b : 自然数} (digits : 自然数 -> 有限集 b)
  结论: 0 <= ofDigits digits
  证明: by
  simp only [ofDigits]
  exact tsum_nonneg fun _ => ofDigitsTerm_nonneg

Depends on / 依赖: ofDigits, ofDigitsTerm_nonneg, tsum_nonneg
-/
theorem ofDigits_nonneg {b : Nat} (digits : Nat -> Fin b) : 0 <= ofDigits digits := by
  simp only [ofDigits]
  exact tsum_nonneg fun _ => ofDigitsTerm_nonneg

/--
theorem `ofDigits_le_one` / 定理 `ofDigits_le_one`

English:
theorem ofDigits_le_one
  given: {b : Nat} (digits : Nat -> Fin b)
  statement: ofDigits digits <= 1
  proof: by
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simp [ofDigits, ofDigitsTerm]
  rify at hb
  convert! Summable.tsum_mono summable_ofDigitsTerm _ (fun _ => ofDigitsTerm_le)
  · simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
    rw [tsum_mul_left]; rw [tsum_geometric_of_lt

中文:
定理 ofDigits_le_one
  条件: {b : 自然数} (digits : 自然数 -> 有限集 b)
  结论: ofDigits digits <= 1
  证明: by
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simp [ofDigits, ofDigitsTerm]
  rify at hb
  convert! Summable.tsum_mono summable_ofDigitsTerm _ (fun _ => ofDigitsTerm_le)
  · simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
    rw [tsum_mul_left]; rw [tsum_geometric_of_lt

Depends on / 依赖: Nat.one_le_of_lt, Summable, Summable.mul_left, Summable.tsum_mono, b_pos, convert, digits, eq_or_lt, inv_pow, mul_assoc, mul_inv, mul_left, ofDigits, ofDigitsTerm, ofDigitsTerm_le, one_le_of_lt, pow_succ, simp_rw, sub_pos, sub_pos.mpr
-/
theorem ofDigits_le_one {b : Nat} (digits : Nat -> Fin b) : ofDigits digits <= 1 := by
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simp [ofDigits, ofDigitsTerm]
  rify at hb
  convert! Summable.tsum_mono summable_ofDigitsTerm _ (fun _ => ofDigitsTerm_le)
  · simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
    rw [tsum_mul_left]; rw [tsum_geometric_of_lt_one (by positivity) (by simp [inv_lt_one_iff₀]; rw [hb])]
    have := sub_pos.mpr hb
    field
  · simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
    refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
    simp [inv_lt_one_iff₀, hb]

/--
theorem `ofDigits_eq_sum_add_ofDigits` / 定理 `ofDigits_eq_sum_add_ofDigits`

English:
theorem ofDigits_eq_sum_add_ofDigits
  given: {b : Nat} (a : Nat -> Fin b) (n : Nat)
  proof: by
  simp only [ofDigits]
  rw [← Summable.sum_add_tsum_nat_add n summable_ofDigitsTerm]; rw [← Summable.tsum_mul_left _ summable_ofDigitsTerm]
  congr
  ext i
  simp only [ofDigitsTerm]
  ring

中文:
定理 ofDigits_eq_sum_add_ofDigits
  条件: {b : 自然数} (a : 自然数 -> 有限集 b) (n : 自然数)
  证明: by
  simp only [ofDigits]
  rw [← Summable.sum_add_tsum_nat_add n summable_ofDigitsTerm]; rw [← Summable.tsum_mul_left _ summable_ofDigitsTerm]
  congr
  ext i
  simp only [ofDigitsTerm]
  ring

Depends on / 依赖: Summable, Summable.sum_add_tsum_nat_add, Summable.tsum_mul_left, ofDigits, ofDigitsTerm, sum_add_tsum_nat_add, summable_ofDigitsTerm, tsum_mul_left
-/
theorem ofDigits_eq_sum_add_ofDigits {b : Nat} (a : Nat -> Fin b) (n : Nat) :
    ofDigits a = (∑ i in Finset.range n, ofDigitsTerm a i) +
      ((b : Real) ^ n)⁻¹ * ofDigits (fun i => a (i + n)) := by
  simp only [ofDigits]
  rw [← Summable.sum_add_tsum_nat_add n summable_ofDigitsTerm]; rw [← Summable.tsum_mul_left _ summable_ofDigitsTerm]
  congr
  ext i
  simp only [ofDigitsTerm]
  ring

/--
theorem `abs_ofDigits_sub_ofDigits_le` / 定理 `abs_ofDigits_sub_ofDigits_le`

English:
theorem abs_ofDigits_sub_ofDigits_le
  statement: {b : Nat} {x y : Nat -> Fin b} {n : Nat}
  proof: by
  rw [ofDigits_eq_sum_add_ofDigits x n]; rw [ofDigits_eq_sum_add_ofDigits y n]
  have : ∑ i in Finset.range n, ofDigitsTerm x i = ∑ i in Finset.range n, ofDigitsTerm y i :=
    Finset.sum_congr rfl fun i hi => by simp [ofDigitsTerm, hxy i (Finset.mem_range.mp hi)]
  rw [this]; rw [add_sub_add_lef

中文:
定理 abs_ofDigits_sub_ofDigits_le
  结论: {b : 自然数} {x y : 自然数 -> 有限集 b} {n : 自然数}
  证明: by
  rw [ofDigits_eq_sum_add_ofDigits x n]; rw [ofDigits_eq_sum_add_ofDigits y n]
  have : ∑ i in Finset.range n, ofDigitsTerm x i = ∑ i in Finset.range n, ofDigitsTerm y i :=
    Finset.sum_congr rfl fun i hi => by simp [ofDigitsTerm, hxy i (Finset.mem_range.mp hi)]
  rw [this]; rw [add_sub_add_lef

Depends on / 依赖: Finset, Finset.mem_range.mp, Finset.range, Finset.sum_congr, abs_mul, abs_of_nonneg, abs_sub_le_of_le_of_le, add_sub_add_left_eq_sub, convert, mem_range, mul_le_of_le_one_right, mul_sub, ofDigitsTerm, ofDigits_eq_sum_add_ofDigits, ofDigits_le_one, ofDigits_nonneg, sum_congr
-/
theorem abs_ofDigits_sub_ofDigits_le {b : Nat} {x y : Nat -> Fin b} {n : Nat}
    (hxy : forall i < n, x i = y i) :
    |ofDigits x - ofDigits y| <= ((b : Real) ^ n)⁻¹ := by
  rw [ofDigits_eq_sum_add_ofDigits x n]; rw [ofDigits_eq_sum_add_ofDigits y n]
  have : ∑ i in Finset.range n, ofDigitsTerm x i = ∑ i in Finset.range n, ofDigitsTerm y i :=
    Finset.sum_congr rfl fun i hi => by simp [ofDigitsTerm, hxy i (Finset.mem_range.mp hi)]
  rw [this]; rw [add_sub_add_left_eq_sub]; rw [← mul_sub]; rw [abs_mul]; rw [abs_of_nonneg (by positivity)]
  apply mul_le_of_le_one_right (by positivity)
  convert!
    abs_sub_le_of_le_of_le (ofDigits_nonneg _) (ofDigits_le_one _) (ofDigits_nonneg _)
      (ofDigits_le_one _)
  simp

/--
Definition of `digits` / `digits` 的定义

English:
definition digits
  signature: (x : Real) (b : Nat) [NeZero b]
  body: fun i => Fin.ofNat _ ⌊x * b ^ (i + 1)⌋₊

中文:
定义 digits
  签名: (x : 实数) (b : 自然数) [NeZero b]
  定义体: fun i => Fin.ofNat _ ⌊x * b ^ (i + 1)⌋₊

Depends on / 依赖: Fin.ofNat
-/
noncomputable def digits (x : Real) (b : Nat) [NeZero b] : Nat -> Fin b :=
fun i => Fin.ofNat _ ⌊x * b ^ (i + 1)⌋₊

/--
theorem `ofDigits_digits_sum_eq` / 定理 `ofDigits_digits_sum_eq`

English:
theorem ofDigits_digits_sum_eq
  given: {x : Real} {b : Nat} [NeZero b] (hx : x in Set.Ico 0 1) (n : Nat)
  proof: by
  have := NeZero.ne b
  induction n with
  | zero => simp [Nat.floor_eq_zero.mpr hx.right]
  | succ n ih =>
    rw [Finset.sum_range_succ]; rw [mul_add]; rw [pow_succ']; rw [mul_assoc]; rw [ih]; rw [ofDigitsTerm]; rw [digits]; rw [← pow_succ']; rw [mul_left_comm]; rw [mul_inv_cancel₀ (by positivi

中文:
定理 ofDigits_digits_sum_eq
  条件: {x : 实数} {b : 自然数} [NeZero b] (hx : x in 集合.左闭右开区间 0 1) (n : 自然数)
  证明: by
  have := NeZero.ne b
  induction n with
  | zero => simp [Nat.floor_eq_zero.mpr hx.right]
  | succ n ih =>
    rw [Finset.sum_range_succ]; rw [mul_add]; rw [pow_succ']; rw [mul_assoc]; rw [ih]; rw [ofDigitsTerm]; rw [digits]; rw [← pow_succ']; rw [mul_left_comm]; rw [mul_inv_cancel₀ (by positivi

Depends on / 依赖: Fin.val_ofNat, Finset, Finset.sum_range_succ, Nat.cast_mul_floor_div_cancel, Nat.div_add_mo, Nat.floor_eq_zero.mpr, NeZero, NeZero.ne, cast_mul_floor_div_cancel, digits, div_add_mo, floor_eq_zero, hx.right, mul_add, mul_assoc, mul_comm, mul_left_comm, mul_one, ofDigitsTerm, pow_succ
-/
theorem ofDigits_digits_sum_eq {x : Real} {b : Nat} [NeZero b] (hx : x in Set.Ico 0 1) (n : Nat) :
    b ^ n * ∑ i in Finset.range n, ofDigitsTerm (digits x b) i = ⌊b ^ n * x⌋₊ := by
  have := NeZero.ne b
  induction n with
  | zero => simp [Nat.floor_eq_zero.mpr hx.right]
  | succ n ih =>
    rw [Finset.sum_range_succ]; rw [mul_add]; rw [pow_succ']; rw [mul_assoc]; rw [ih]; rw [ofDigitsTerm]; rw [digits]; rw [← pow_succ']; rw [mul_left_comm]; rw [mul_inv_cancel₀ (by positivity)]; rw [mul_one]; rw [mul_comm x]; rw [pow_succ']; rw [mul_assoc]
    set y := (b : Real) ^ n * x
    norm_cast
    rw [← Nat.cast_mul_floor_div_cancel (a := y) (show b != 0 by lia)]; rw [Fin.val_ofNat]; rw [Nat.div_add_mod]

/--
theorem `le_sum_ofDigitsTerm_digits` / 定理 `le_sum_ofDigitsTerm_digits`

English:
theorem le_sum_ofDigitsTerm_digits
  statement: {x : Real} {b : Nat} [NeZero b]
  proof: by
  have := NeZero.pos b
  have := ofDigits_digits_sum_eq (b := b) hx n
  have h_le := Nat.lt_floor_add_one (b ^ n * x)
  rw [← this] at h_le
  rw [← mul_le_mul_iff_right₀ (show 0 < (b : Real) ^ n by positivity)]; rw [mul_sub]; rw [inv_pow]; rw [mul_inv_cancel₀ (by positivity)]
  linarith

中文:
定理 le_sum_ofDigitsTerm_digits
  结论: {x : 实数} {b : 自然数} [NeZero b]
  证明: by
  have := NeZero.pos b
  have := ofDigits_digits_sum_eq (b := b) hx n
  have h_le := Nat.lt_floor_add_one (b ^ n * x)
  rw [← this] at h_le
  rw [← mul_le_mul_iff_right₀ (show 0 < (b : Real) ^ n by positivity)]; rw [mul_sub]; rw [inv_pow]; rw [mul_inv_cancel₀ (by positivity)]
  linarith

Depends on / 依赖: Nat.lt_floor_add_one, NeZero, NeZero.pos, h_le, inv_pow, lt_floor_add_one, mul_sub, ofDigits_digits_sum_eq
-/
theorem le_sum_ofDigitsTerm_digits {x : Real} {b : Nat} [NeZero b]
    (hx : x in Set.Ico 0 1) (n : Nat) :
    x - (b⁻¹ : Real) ^ n <= ∑ i in Finset.range n, ofDigitsTerm (digits x b) i := by
  have := NeZero.pos b
  have := ofDigits_digits_sum_eq (b := b) hx n
  have h_le := Nat.lt_floor_add_one (b ^ n * x)
  rw [← this] at h_le
  rw [← mul_le_mul_iff_right₀ (show 0 < (b : Real) ^ n by positivity)]; rw [mul_sub]; rw [inv_pow]; rw [mul_inv_cancel₀ (by positivity)]
  linarith

/--
theorem `sum_ofDigitsTerm_digits_le` / 定理 `sum_ofDigitsTerm_digits_le`

English:
theorem sum_ofDigitsTerm_digits_le
  statement: {x : Real} {b : Nat} [NeZero b]
  proof: by
  have := ofDigits_digits_sum_eq (b := b) hx n
  have h_le := Nat.floor_le (a := b ^ n * x) (by have := hx.left; positivity)
  have hb := NeZero.ne b
  rw [← this]; rw [mul_le_mul_iff_of_pos_left (by positivity)] at h_le
  exact h_le

中文:
定理 sum_ofDigitsTerm_digits_le
  结论: {x : 实数} {b : 自然数} [NeZero b]
  证明: by
  have := ofDigits_digits_sum_eq (b := b) hx n
  have h_le := Nat.floor_le (a := b ^ n * x) (by have := hx.left; positivity)
  have hb := NeZero.ne b
  rw [← this]; rw [mul_le_mul_iff_of_pos_left (by positivity)] at h_le
  exact h_le

Depends on / 依赖: Nat.floor_le, NeZero, NeZero.ne, floor_le, h_le, hx.left, mul_le_mul_iff_of_pos_left, ofDigits_digits_sum_eq
-/
theorem sum_ofDigitsTerm_digits_le {x : Real} {b : Nat} [NeZero b]
    (hx : x in Set.Ico 0 1) (n : Nat) :
    ∑ i in Finset.range n, ofDigitsTerm (digits x b) i <= x := by
  have := ofDigits_digits_sum_eq (b := b) hx n
  have h_le := Nat.floor_le (a := b ^ n * x) (by have := hx.left; positivity)
  have hb := NeZero.ne b
  rw [← this]; rw [mul_le_mul_iff_of_pos_left (by positivity)] at h_le
  exact h_le

/--
theorem `hasSum_ofDigitsTerm_digits` / 定理 `hasSum_ofDigitsTerm_digits`

English:
theorem hasSum_ofDigitsTerm_digits
  given: (x : Real) {b : Nat} [NeZero b] (hb : 1 < b) (hx : x in Set.Ico 0 1)
  proof: by
  rw [hasSum_iff_tendsto_nat_of_summable_norm (by exact summable_ofDigitsTerm.abs)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
    (le_sum_ofDigitsTerm_digits hx) (sum_ofDigitsTerm_digits_le hx)
  convert! tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_abs_lt

中文:
定理 hasSum_ofDigitsTerm_digits
  条件: (x : 实数) {b : 自然数} [NeZero b] (hb : 1 < b) (hx : x in 集合.左闭右开区间 0 1)
  证明: by
  rw [hasSum_iff_tendsto_nat_of_summable_norm (by exact summable_ofDigitsTerm.abs)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
    (le_sum_ofDigitsTerm_digits hx) (sum_ofDigitsTerm_digits_le hx)
  convert! tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_abs_lt

Depends on / 依赖: abs_of_nonneg, convert, hasSum_iff_tendsto_nat_of_summable_norm, le_sum_ofDigitsTerm_digits, sum_ofDigitsTerm_digits_le, summable_ofDigitsTerm, summable_ofDigitsTerm.abs, tendsto_const_nhds, tendsto_const_nhds.sub, tendsto_of_tendsto_of_tendsto_of_le_of_le, tendsto_pow_atTop_nhds_zero_of_abs_lt_one
-/
theorem hasSum_ofDigitsTerm_digits (x : Real) {b : Nat} [NeZero b] (hb : 1 < b) (hx : x in Set.Ico 0 1) :
    HasSum (ofDigitsTerm (digits x b)) x := by
  rw [hasSum_iff_tendsto_nat_of_summable_norm (by exact summable_ofDigitsTerm.abs)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
    (le_sum_ofDigitsTerm_digits hx) (sum_ofDigitsTerm_digits_le hx)
  convert! tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_abs_lt_one _)
  · simp
  · simp [abs_of_nonneg, inv_lt_one_iff₀, hb]

/--
theorem `ofDigits_digits` / 定理 `ofDigits_digits`

English:
theorem ofDigits_digits
  given: {b : Nat} [NeZero b] {x : Real} (hb : 1 < b) (hx : x in Set.Ico 0 1)
  proof: by
  simp only [ofDigits]
  rw [← Summable.hasSum_iff]
  · exact hasSum_ofDigitsTerm_digits x hb hx
  · exact summable_ofDigitsTerm

中文:
定理 ofDigits_digits
  条件: {b : 自然数} [NeZero b] {x : 实数} (hb : 1 < b) (hx : x in 集合.左闭右开区间 0 1)
  证明: by
  simp only [ofDigits]
  rw [← Summable.hasSum_iff]
  · exact hasSum_ofDigitsTerm_digits x hb hx
  · exact summable_ofDigitsTerm

Depends on / 依赖: Summable, Summable.hasSum_iff, hasSum_iff, hasSum_ofDigitsTerm_digits, ofDigits, summable_ofDigitsTerm
-/
theorem ofDigits_digits {b : Nat} [NeZero b] {x : Real} (hb : 1 < b) (hx : x in Set.Ico 0 1) :
    ofDigits (digits x b) = x := by
  simp only [ofDigits]
  rw [← Summable.hasSum_iff]
  · exact hasSum_ofDigitsTerm_digits x hb hx
  · exact summable_ofDigitsTerm

/--
theorem `ofDigits_const_last_eq_one` / 定理 `ofDigits_const_last_eq_one`

English:
theorem ofDigits_const_last_eq_one
  given: (b : Nat) [NeZero b]
  proof: by
  have : 1 < |(b + 1 : Real)| := by
    rw [← Nat.cast_add_one]; rw [abs_of_nonneg (Nat.cast_nonneg _)]
    simp [NeZero.pos b]
  simp only [ofDigits, ofDigitsTerm, ← inv_pow]
  rw [Summable.tsum_mul_left]
  · rw [geom_series_succ _ (by simp [inv_lt_one_iff₀, this]),
      tsum_geometric_of_lt_on

中文:
定理 ofDigits_const_last_eq_one
  条件: (b : 自然数) [NeZero b]
  证明: by
  have : 1 < |(b + 1 : Real)| := by
    rw [← Nat.cast_add_one]; rw [abs_of_nonneg (Nat.cast_nonneg _)]
    simp [NeZero.pos b]
  simp only [ofDigits, ofDigitsTerm, ← inv_pow]
  rw [Summable.tsum_mul_left]
  · rw [geom_series_succ _ (by simp [inv_lt_one_iff₀, this]),
      tsum_geometric_of_lt_on

Depends on / 依赖: Nat.cast_add_one, Nat.cast_nonneg, NeZero, NeZero.ne, NeZero.pos, Summable, Summable.tsum_mul_left, abs_of_nonneg, cast_add_one, cast_nonneg, geom_series_succ, inv_pow, mod_cast, ofDigits, ofDigitsTerm, summable_geom, summable_nat_add_iff, tsum_geometric_of_lt_one, tsum_mul_left
-/
theorem ofDigits_const_last_eq_one (b : Nat) [NeZero b] :
    ofDigits (fun _ => Fin.last b) = 1 := by
  have : 1 < |(b + 1 : Real)| := by
    rw [← Nat.cast_add_one]; rw [abs_of_nonneg (Nat.cast_nonneg _)]
    simp [NeZero.pos b]
  simp only [ofDigits, ofDigitsTerm, ← inv_pow]
  rw [Summable.tsum_mul_left]
  · rw [geom_series_succ _ (by simp [inv_lt_one_iff₀, this]),
      tsum_geometric_of_lt_one (by positivity) (by simp [inv_lt_one_iff₀, NeZero.pos b])]
    push_cast
    have : (b : Real) != 0 := mod_cast NeZero.ne b
    field [*]
  · rw [summable_nat_add_iff (f := fun n => ((b + 1 : Nat) : Real)⁻¹ ^ n) 1]
    apply summable_geometric_of_lt_one (by positivity) (by simp [inv_lt_one_iff₀, NeZero.pos b])

/--
theorem `ofDigits_const_last_eq_one'` / 定理 `ofDigits_const_last_eq_one'`

English:
theorem ofDigits_const_last_eq_one'
  given: {b : Nat} (hb : 1 < b)
  proof: by
  convert! ofDigits_const_last_eq_one (b - 1)
  · grind
  · constructor
    grind

中文:
定理 ofDigits_const_last_eq_one'
  条件: {b : 自然数} (hb : 1 < b)
  证明: by
  convert! ofDigits_const_last_eq_one (b - 1)
  · grind
  · constructor
    grind

Depends on / 依赖: convert, ofDigits_const_last_eq_one
-/
theorem ofDigits_const_last_eq_one' {b : Nat} (hb : 1 < b) :
    ofDigits (fun _ => (⟨b - 1, Nat.sub_one_lt_of_lt hb⟩ : Fin b)) = 1 := by
  convert! ofDigits_const_last_eq_one (b - 1)
  · grind
  · constructor
    grind

/--
theorem `ofDigits_SurjOn` / 定理 `ofDigits_SurjOn`

English:
theorem ofDigits_SurjOn
  given: {b : Nat} (hb : 1 < b)
  proof: by
  have : NeZero b := ⟨by grind⟩
  intro y hy
  by_cases hy' : y in Set.Ico 0 1
  · use digits y b
    simp [ofDigits_digits hb hy']
  · simp only [Set.image_univ, show y = 1 by grind, Set.mem_range]
    exact ⟨_, ofDigits_const_last_eq_one' hb⟩

中文:
定理 ofDigits_SurjOn
  条件: {b : 自然数} (hb : 1 < b)
  证明: by
  have : NeZero b := ⟨by grind⟩
  intro y hy
  by_cases hy' : y in Set.Ico 0 1
  · use digits y b
    simp [ofDigits_digits hb hy']
  · simp only [Set.image_univ, show y = 1 by grind, Set.mem_range]
    exact ⟨_, ofDigits_const_last_eq_one' hb⟩

Depends on / 依赖: NeZero, Set.Icc, Set.Ico, Set.image_univ, Set.mem_range, Set.univ, digits, image_univ, mem_range, ofDigits_const_last_eq_one, ofDigits_digits
-/
theorem ofDigits_SurjOn {b : Nat} (hb : 1 < b) :
    Set.SurjOn (ofDigits (b := b)) Set.univ (Set.Icc 0 1) := by
  have : NeZero b := ⟨by grind⟩
  intro y hy
  by_cases hy' : y in Set.Ico 0 1
  · use digits y b
    simp [ofDigits_digits hb hy']
  · simp only [Set.image_univ, show y = 1 by grind, Set.mem_range]
    exact ⟨_, ofDigits_const_last_eq_one' hb⟩

/--
theorem `continuous_ofDigits` / 定理 `continuous_ofDigits`

English:
theorem continuous_ofDigits
  given: {b : Nat}
  statement: Continuous (@ofDigits b)
  proof: by
  match b with
  | 0 => fun_prop
  | 1 => fun_prop
  | n + 2 =>
    obtain ⟨hb0, hb⟩ : 0 < n + 2 ∧ 1 < n + 2 := by grind
    generalize n + 2 = b at hb
    rify at hb0 hb
    refine continuous_tsum (u := fun i => (b : Real)⁻¹ ^ i) ?_ ?_ fun n x => ?_
    · simp only [ofDigitsTerm]
      fun_prop


中文:
定理 continuous_ofDigits
  条件: {b : 自然数}
  结论: 连续 (@ofDigits b)
  证明: by
  match b with
  | 0 => fun_prop
  | 1 => fun_prop
  | n + 2 =>
    obtain ⟨hb0, hb⟩ : 0 < n + 2 ∧ 1 < n + 2 := by grind
    generalize n + 2 = b at hb
    rify at hb0 hb
    refine continuous_tsum (u := fun i => (b : Real)⁻¹ ^ i) ?_ ?_ fun n x => ?_
    · simp only [ofDigitsTerm]
      fun_prop


Depends on / 依赖: abs_of_nonneg, continuous_tsum, fun_prop, generalize, inv_pow, norm_eq_abs, ofDigitsTerm, ofDigitsTerm_le, ofDigitsTerm_le.trans, ofDigitsTerm_nonneg, summable_geometric_of_lt_one
-/
theorem continuous_ofDigits {b : Nat} : Continuous (@ofDigits b) := by
  match b with
  | 0 => fun_prop
  | 1 => fun_prop
  | n + 2 =>
    obtain ⟨hb0, hb⟩ : 0 < n + 2 ∧ 1 < n + 2 := by grind
    generalize n + 2 = b at hb
    rify at hb0 hb
    refine continuous_tsum (u := fun i => (b : Real)⁻¹ ^ i) ?_ ?_ fun n x => ?_
    · simp only [ofDigitsTerm]
      fun_prop
    · exact summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb)
    · simp only [norm_eq_abs, abs_of_nonneg ofDigitsTerm_nonneg, inv_pow]
      apply ofDigitsTerm_le.trans
      calc
        _ <= b * ((b : Real) ^ (n + 1))⁻¹ := by
          gcongr
          linarith
        _ = _ := by
          grind

end Real
