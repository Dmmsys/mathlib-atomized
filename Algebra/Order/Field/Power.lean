/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn, Sabbir Rahman
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Tactic.Positivity.Core

/-!
# Lemmas about powers in ordered fields.
-/

public section


variable {α : Type*}

open Function Int

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : Int}

/--
theorem `Even.zpow_nonneg` / 定理 `Even.zpow_nonneg`

English:
theorem Even.zpow_nonneg
  given: (hn : Even n) (a : α)
  statement: 0 <= a ^ n
  proof: by
  obtain ⟨k, rfl⟩ := hn; rw [zpow_add' (by simp [em'])]; exact mul_self_nonneg _

中文:
定理 Even.zpow_nonneg
  条件: (hn : Even n) (a : α)
  结论: 0 <= a ^ n
  证明: by
  obtain ⟨k, rfl⟩ := hn; rw [zpow_add' (by simp [em'])]; exact mul_self_nonneg _
-/
protected theorem Even.zpow_nonneg (hn : Even n) (a : α) : 0 <= a ^ n := by
  obtain ⟨k, rfl⟩ := hn; rw [zpow_add' (by simp [em'])]; exact mul_self_nonneg _

/--
lemma `zpow_two_nonneg` / 引理 `zpow_two_nonneg`

English:
lemma zpow_two_nonneg
  given: (a : α)
  statement: 0 <= a ^ (2 : Int)
  proof: even_two.zpow_nonneg _

中文:
引理 zpow_two_nonneg
  条件: (a : α)
  结论: 0 <= a ^ (2 : 整数)
  证明: even_two.zpow_nonneg _

Depends on / 依赖: even_two, even_two.zpow_nonneg, zpow_nonneg
-/
lemma zpow_two_nonneg (a : α) : 0 <= a ^ (2 : Int) := even_two.zpow_nonneg _

/--
lemma `zpow_neg_two_nonneg` / 引理 `zpow_neg_two_nonneg`

English:
lemma zpow_neg_two_nonneg
  given: (a : α)
  statement: 0 <= a ^ (-2 : Int)
  proof: even_neg_two.zpow_nonneg _

中文:
引理 zpow_neg_two_nonneg
  条件: (a : α)
  结论: 0 <= a ^ (-2 : 整数)
  证明: even_neg_two.zpow_nonneg _

Depends on / 依赖: even_neg_two, even_neg_two.zpow_nonneg, zpow_nonneg
-/
lemma zpow_neg_two_nonneg (a : α) : 0 <= a ^ (-2 : Int) := even_neg_two.zpow_nonneg _

/--
lemma `Even.zpow_pos` / 引理 `Even.zpow_pos`

English:
lemma Even.zpow_pos
  given: (hn : Even n) (ha : a != 0)
  statement: 0 < a ^ n
  proof: (hn.zpow_nonneg _).lt_of_ne' (zpow_ne_zero _ ha)

中文:
引理 Even.zpow_pos
  条件: (hn : Even n) (ha : a != 0)
  结论: 0 < a ^ n
  证明: (hn.zpow_nonneg _).lt_of_ne' (zpow_ne_zero _ ha)
-/
protected lemma Even.zpow_pos (hn : Even n) (ha : a != 0) : 0 < a ^ n :=
  (hn.zpow_nonneg _).lt_of_ne' (zpow_ne_zero _ ha)

/--
lemma `zpow_two_pos_of_ne_zero` / 引理 `zpow_two_pos_of_ne_zero`

English:
lemma zpow_two_pos_of_ne_zero
  given: (ha : a != 0)
  statement: 0 < a ^ (2 : Int)
  proof: even_two.zpow_pos ha

中文:
引理 zpow_two_pos_of_ne_zero
  条件: (ha : a != 0)
  结论: 0 < a ^ (2 : 整数)
  证明: even_two.zpow_pos ha

Depends on / 依赖: even_two, even_two.zpow_pos, zpow_pos
-/
lemma zpow_two_pos_of_ne_zero (ha : a != 0) : 0 < a ^ (2 : Int) := even_two.zpow_pos ha

/--
theorem `Even.zpow_pos_iff` / 定理 `Even.zpow_pos_iff`

English:
theorem Even.zpow_pos_iff
  given: (hn : Even n) (h : n != 0)
  statement: 0 < a ^ n ↔ a != 0
  proof: by
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add' (by simp [em']), mul_self_pos, zpow_ne_zero_iff (by simpa using h)]

中文:
定理 Even.zpow_pos_iff
  条件: (hn : Even n) (h : n != 0)
  结论: 0 < a ^ n ↔ a != 0
  证明: by
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add' (by simp [em']), mul_self_pos, zpow_ne_zero_iff (by simpa using h)]

Depends on / 依赖: mul_self_pos, zpow_add, zpow_ne_zero_iff
-/
theorem Even.zpow_pos_iff (hn : Even n) (h : n != 0) : 0 < a ^ n ↔ a != 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add' (by simp [em']), mul_self_pos, zpow_ne_zero_iff (by simpa using h)]

/--
theorem `Odd.zpow_neg_iff` / 定理 `Odd.zpow_neg_iff`

English:
theorem Odd.zpow_neg_iff
  given: (hn : Odd n)
  statement: a ^ n < 0 ↔ a < 0
  proof: by
  refine ⟨lt_imp_lt_of_le_imp_le (zpow_nonneg · _), fun ha => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add_one₀ ha.ne]
  exact mul_neg_of_pos_of_neg (Even.zpow_pos (even_two_mul _) ha.ne) ha

中文:
定理 Odd.zpow_neg_iff
  条件: (hn : Odd n)
  结论: a ^ n < 0 ↔ a < 0
  证明: by
  refine ⟨lt_imp_lt_of_le_imp_le (zpow_nonneg · _), fun ha => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add_one₀ ha.ne]
  exact mul_neg_of_pos_of_neg (Even.zpow_pos (even_two_mul _) ha.ne) ha

Depends on / 依赖: Even.zpow_pos, even_two_mul, ha.ne, lt_imp_lt_of_le_imp_le, mul_neg_of_pos_of_neg, zpow_nonneg, zpow_pos
-/
theorem Odd.zpow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (zpow_nonneg · _), fun ha => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add_one₀ ha.ne]
  exact mul_neg_of_pos_of_neg (Even.zpow_pos (even_two_mul _) ha.ne) ha

/--
lemma `Odd.zpow_nonneg_iff` / 引理 `Odd.zpow_nonneg_iff`

English:
lemma Odd.zpow_nonneg_iff
  given: (hn : Odd n)
  statement: 0 <= a ^ n ↔ 0 <= a
  proof: le_iff_le_iff_lt_iff_lt.2 hn.zpow_neg_iff

中文:
引理 Odd.zpow_nonneg_iff
  条件: (hn : Odd n)
  结论: 0 <= a ^ n ↔ 0 <= a
  证明: le_iff_le_iff_lt_iff_lt.2 hn.zpow_neg_iff
-/
protected lemma Odd.zpow_nonneg_iff (hn : Odd n) : 0 <= a ^ n ↔ 0 <= a :=
  le_iff_le_iff_lt_iff_lt.2 hn.zpow_neg_iff

/--
theorem `Odd.zpow_nonpos_iff` / 定理 `Odd.zpow_nonpos_iff`

English:
theorem Odd.zpow_nonpos_iff
  given: (hn : Odd n)
  statement: a ^ n <= 0 ↔ a <= 0
  proof: by
  rw [le_iff_lt_or_eq]; rw [le_iff_lt_or_eq]; rw [hn.zpow_neg_iff]; rw [zpow_eq_zero_iff]
  rintro rfl
  exact Int.not_even_iff_odd.2 hn .zero

中文:
定理 Odd.zpow_nonpos_iff
  条件: (hn : Odd n)
  结论: a ^ n <= 0 ↔ a <= 0
  证明: by
  rw [le_iff_lt_or_eq]; rw [le_iff_lt_or_eq]; rw [hn.zpow_neg_iff]; rw [zpow_eq_zero_iff]
  rintro rfl
  exact Int.not_even_iff_odd.2 hn .zero

Depends on / 依赖: Int.not_even_iff_odd, hn.zpow_neg_iff, le_iff_lt_or_eq, not_even_iff_odd, zpow_eq_zero_iff, zpow_neg_iff
-/
theorem Odd.zpow_nonpos_iff (hn : Odd n) : a ^ n <= 0 ↔ a <= 0 := by
  rw [le_iff_lt_or_eq]; rw [le_iff_lt_or_eq]; rw [hn.zpow_neg_iff]; rw [zpow_eq_zero_iff]
  rintro rfl
  exact Int.not_even_iff_odd.2 hn .zero

/--
lemma `Odd.zpow_pos_iff` / 引理 `Odd.zpow_pos_iff`

English:
lemma Odd.zpow_pos_iff
  given: (hn : Odd n)
  statement: 0 < a ^ n ↔ 0 < a
  proof: lt_iff_lt_of_le_iff_le hn.zpow_nonpos_iff

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff

alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff

@[simp]

中文:
引理 Odd.zpow_pos_iff
  条件: (hn : Odd n)
  结论: 0 < a ^ n ↔ 0 < a
  证明: lt_iff_lt_of_le_iff_le hn.zpow_nonpos_iff

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff

alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff

@[simp]

Depends on / 依赖: hn.zpow_nonpos_iff, lt_iff_lt_of_le_iff_le, zpow_nonpos_iff
-/
lemma Odd.zpow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.zpow_nonpos_iff

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff

alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff

@[simp]
/--
theorem `abs_zpow` / 定理 `abs_zpow`

English:
theorem abs_zpow
  given: (a : α) (p : Int)
  statement: |a ^ p| = |a| ^ p
  proof: map_zpow₀ absHom a p

中文:
定理 abs_zpow
  条件: (a : α) (p : 整数)
  结论: |a ^ p| = |a| ^ p
  证明: map_zpow₀ absHom a p

Depends on / 依赖: absHom
-/
theorem abs_zpow (a : α) (p : Int) : |a ^ p| = |a| ^ p := map_zpow₀ absHom a p

/--
theorem `abs_neg_one_zpow` / 定理 `abs_neg_one_zpow`

English:
theorem abs_neg_one_zpow
  given: (p : Int)
  statement: |(-1 : α) ^ p| = 1
  proof: by simp

omit [IsStrictOrderedRing α] in

中文:
定理 abs_neg_one_zpow
  条件: (p : 整数)
  结论: |(-1 : α) ^ p| = 1
  证明: by simp

omit [IsStrictOrderedRing α] in
-/
theorem abs_neg_one_zpow (p : Int) : |(-1 : α) ^ p| = 1 := by simp

omit [IsStrictOrderedRing α] in
/--
theorem `Even.zpow_abs` / 定理 `Even.zpow_abs`

English:
theorem Even.zpow_abs
  given: {p : Int} (hp : Even p) (a : α)
  statement: |a| ^ p = a ^ p
  proof: by
  rcases abs_choice a with h | h <;> simp only [h, hp.neg_zpow _]

中文:
定理 Even.zpow_abs
  条件: {p : 整数} (hp : Even p) (a : α)
  结论: |a| ^ p = a ^ p
  证明: by
  rcases abs_choice a with h | h <;> simp only [h, hp.neg_zpow _]

Depends on / 依赖: abs_choice, hp.neg_zpow, neg_zpow
-/
theorem Even.zpow_abs {p : Int} (hp : Even p) (a : α) : |a| ^ p = a ^ p := by
  rcases abs_choice a with h | h <;> simp only [h, hp.neg_zpow _]

/--
lemma `zpow_eq_zpow_iff_of_ne_zero₀` / 引理 `zpow_eq_zpow_iff_of_ne_zero₀`

English:
lemma zpow_eq_zpow_iff_of_ne_zero₀
  given: (hn : n != 0)
  statement: a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n
  proof: match n with
  | Int.ofNat m => by
    simp only [Int.ofNat_eq_natCast, ne_eq, Nat.cast_eq_zero, zpow_natCast, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, ne_eq, neg_eq_zero, Nat.cast_eq_zero, zpow_neg, zpow_natCast,
      inv_inj, even_neg, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn

中文:
引理 zpow_eq_zpow_iff_of_ne_zero₀
  条件: (hn : n != 0)
  结论: a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n
  证明: match n with
  | Int.ofNat m => by
    simp only [Int.ofNat_eq_natCast, ne_eq, Nat.cast_eq_zero, zpow_natCast, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, ne_eq, neg_eq_zero, Nat.cast_eq_zero, zpow_neg, zpow_natCast,
      inv_inj, even_neg, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn

Depends on / 依赖: Int.even_coe_nat, Int.negSucc, Int.ofNat, Int.ofNat_eq_natCast, Nat.cast_eq_zero, cast_eq_zero, even_coe_nat, even_neg, inv_inj, ne_eq, negSucc, neg_eq_zero, neg_ofNat_succ, ofNat_eq_natCast, pow_eq_pow_iff_of_ne_zero, zpow_natCast, zpow_neg
-/
lemma zpow_eq_zpow_iff_of_ne_zero₀ (hn : n != 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n :=
  match n with
  | Int.ofNat m => by
    simp only [Int.ofNat_eq_natCast, ne_eq, Nat.cast_eq_zero, zpow_natCast, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, ne_eq, neg_eq_zero, Nat.cast_eq_zero, zpow_neg, zpow_natCast,
      inv_inj, even_neg, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn

/--
lemma `zpow_eq_zpow_iff_cases₀` / 引理 `zpow_eq_zpow_iff_cases₀`

English:
lemma zpow_eq_zpow_iff_cases₀
  statement: a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n
  proof: by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [zpow_eq_zpow_iff_of_ne_zero₀, *]

中文:
引理 zpow_eq_zpow_iff_cases₀
  结论: a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n
  证明: by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [zpow_eq_zpow_iff_of_ne_zero₀, *]

Depends on / 依赖: eq_or_ne
-/
lemma zpow_eq_zpow_iff_cases₀ : a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [zpow_eq_zpow_iff_of_ne_zero₀, *]

/--
lemma `zpow_eq_one_iff_of_ne_zero₀` / 引理 `zpow_eq_one_iff_of_ne_zero₀`

English:
lemma zpow_eq_one_iff_of_ne_zero₀
  given: (hn : n != 0)
  statement: a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n
  proof: by
  simp [← zpow_eq_zpow_iff_of_ne_zero₀ hn]

中文:
引理 zpow_eq_one_iff_of_ne_zero₀
  条件: (hn : n != 0)
  结论: a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n
  证明: by
  simp [← zpow_eq_zpow_iff_of_ne_zero₀ hn]
-/
lemma zpow_eq_one_iff_of_ne_zero₀ (hn : n != 0) : a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← zpow_eq_zpow_iff_of_ne_zero₀ hn]

/--
lemma `zpow_eq_one_iff_cases₀` / 引理 `zpow_eq_one_iff_cases₀`

English:
lemma zpow_eq_one_iff_cases₀
  statement: a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n
  proof: by
  simp [← zpow_eq_zpow_iff_cases₀]

中文:
引理 zpow_eq_one_iff_cases₀
  结论: a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n
  证明: by
  simp [← zpow_eq_zpow_iff_cases₀]
-/
lemma zpow_eq_one_iff_cases₀ : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← zpow_eq_zpow_iff_cases₀]

/--
lemma `zpow_eq_neg_zpow_iff₀` / 引理 `zpow_eq_neg_zpow_iff₀`

English:
lemma zpow_eq_neg_zpow_iff₀
  given: (hb : b != 0)
  statement: a ^ n = -b ^ n ↔ a = -b ∧ Odd n
  proof: match n with
  | Int.ofNat m => by
    simp [pow_eq_neg_pow_iff, hb]
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, zpow_neg, ← inv_neg, pow_eq_neg_pow_iff hb, inv_inj,
      zpow_natCast]
    simp [parity_simps]

中文:
引理 zpow_eq_neg_zpow_iff₀
  条件: (hb : b != 0)
  结论: a ^ n = -b ^ n ↔ a = -b ∧ Odd n
  证明: match n with
  | Int.ofNat m => by
    simp [pow_eq_neg_pow_iff, hb]
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, zpow_neg, ← inv_neg, pow_eq_neg_pow_iff hb, inv_inj,
      zpow_natCast]
    simp [parity_simps]

Depends on / 依赖: Int.negSucc, Int.ofNat, inv_inj, inv_neg, negSucc, neg_ofNat_succ, parity_simps, pow_eq_neg_pow_iff, zpow_natCast, zpow_neg
-/
lemma zpow_eq_neg_zpow_iff₀ (hb : b != 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n :=
  match n with
  | Int.ofNat m => by
    simp [pow_eq_neg_pow_iff, hb]
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, zpow_neg, ← inv_neg, pow_eq_neg_pow_iff hb, inv_inj,
      zpow_natCast]
    simp [parity_simps]

/--
lemma `zpow_eq_neg_one_iff₀` / 引理 `zpow_eq_neg_one_iff₀`

English:
lemma zpow_eq_neg_one_iff₀
  statement: a ^ n = -1 ↔ a = -1 ∧ Odd n
  proof: by
  simpa using zpow_eq_neg_zpow_iff₀ (α := α) one_ne_zero

中文:
引理 zpow_eq_neg_one_iff₀
  结论: a ^ n = -1 ↔ a = -1 ∧ Odd n
  证明: by
  simpa using zpow_eq_neg_zpow_iff₀ (α := α) one_ne_zero

Depends on / 依赖: one_ne_zero
-/
lemma zpow_eq_neg_one_iff₀ : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using zpow_eq_neg_zpow_iff₀ (α := α) one_ne_zero

/-! ### Bernoulli's inequality -/

/--
theorem `Nat.cast_le_pow_sub_div_sub` / 定理 `Nat.cast_le_pow_sub_div_sub`

English:
theorem Nat.cast_le_pow_sub_div_sub
  given: (H : 1 < a) (n : Nat)
  statement: (n : α) <= (a ^ n - 1) / (a - 1)
  proof: (le_div_iff₀ (sub_pos.2 H)).2
le_sub_left_of_add_le one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

中文:
定理 自然数.cast_le_pow_sub_div_sub
  条件: (H : 1 < a) (n : 自然数)
  结论: (n : α) <= (a ^ n - 1) / (a - 1)
  证明: (le_div_iff₀ (sub_pos.2 H)).2
le_sub_left_of_add_le one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

Depends on / 依赖: H.le, le_sub_left_of_add_le, neg_le_self, one_add_mul_sub_le_pow, sub_pos, zero_le_one
-/
theorem Nat.cast_le_pow_sub_div_sub (H : 1 < a) (n : Nat) : (n : α) <= (a ^ n - 1) / (a - 1) :=
(le_div_iff₀ (sub_pos.2 H)).2
le_sub_left_of_add_le one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

/--
theorem `Nat.cast_le_pow_div_sub` / 定理 `Nat.cast_le_pow_div_sub`

English:
theorem Nat.cast_le_pow_div_sub
  given: (H : 1 < a) (n : Nat)
  statement: (n : α) <= a ^ n / (a - 1)
  proof: (n.cast_le_pow_sub_div_sub H).trans
    div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.2 H.le)

中文:
定理 自然数.cast_le_pow_div_sub
  条件: (H : 1 < a) (n : 自然数)
  结论: (n : α) <= a ^ n / (a - 1)
  证明: (n.cast_le_pow_sub_div_sub H).trans
    div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.2 H.le)

Depends on / 依赖: H.le, cast_le_pow_sub_div_sub, div_le_div_of_nonneg_right, n.cast_le_pow_sub_div_sub, sub_le_self, sub_nonneg, zero_le_one
-/
theorem Nat.cast_le_pow_div_sub (H : 1 < a) (n : Nat) : (n : α) <= a ^ n / (a - 1) :=
(n.cast_le_pow_sub_div_sub H).trans
    div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.2 H.le)

end LinearOrderedField

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- The `positivity` extension which identifies expressions of the form `a ^ (b : ℤ)`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ ^ (_ : Int), Pow.pow _ (_ : Int)]
meta def evalZPow : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app _ (a : Q($α))) (b : Q(Int)) ← withReducible (whnf e) | throwError "not ^"
  match (dependent := true) pα? with
  | none =>
    match ← core zα pα? a with
    | .nonzero pa =>
      let _a ← synthInstanceQ q(GroupWithZero $α)
      assumeInstancesCommute
haveI' : e =Q a ^ b := ⟨⟩
      pure (.nonzero q(zpow_ne_zero $b $pa))
    | _ => pure .none
  | some pα =>
    let result ← catchNone do
      let _a ← synthInstanceQ q(Field $α)
      let _a ← synthInstanceQ q(LinearOrder $α)
      let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      match ← whnfR b with
      | .app (.app (.app (.const `OfNat.ofNat _) _) (.lit (Literal.natVal n))) _ =>
        guard (n % 2 = 0)
        have m : Q(Nat) := mkRawNatLit (n / 2)
haveI' : b =Q m + m := ⟨⟩
haveI' : e =Q a ^ b := ⟨⟩
        pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a))
      | .app (.app (.app (.const `Neg.neg _) _) _) b' =>
        let b' ← whnfR b'
        let .true := b'.isAppOfArity ``OfNat.ofNat 3 | throwError "not a ^ -n where n is a literal"
        let some n := (b'.getRevArg! 1).rawNatLit? | throwError "not a ^ -n where n is a literal"
        guard (n % 2 = 0)
        have m : Q(Nat) := mkRawNatLit (n / 2)
haveI' : b =Q (-$m) + (-$m) := ⟨⟩
haveI' : e =Q a ^ b := ⟨⟩
        pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a))
      | _ => throwError "not a ^ n where n is a literal or a negated literal"
    orElse result do
      let ra ← core zα pα a
      let ofNonneg (pa : Q(0 <= $a))
          (_oα : Q(Semifield $α)) (_oα : Q(LinearOrder $α)) (_oα : Q(IsStrictOrderedRing $α)) :
          MetaM (Strictness zα e pα) := do
haveI' : e =Q a ^ b := ⟨⟩
        assumeInstancesCommute
        pure (.nonnegative q(zpow_nonneg $pa $b))
      let ofNonzero (pa : Q($a != 0)) (_oα : Q(GroupWithZero $α)) : MetaM (Strictness zα e pα) := do
haveI' : e =Q a ^ b := ⟨⟩
        let _a ← synthInstanceQ q(GroupWithZero $α)
        assumeInstancesCommute
        pure (.nonzero q(zpow_ne_zero $b $pa))
      match ra with
      | .positive pa =>
        try
          let _a ← synthInstanceQ q(Semifield $α)
          let _a ← synthInstanceQ q(LinearOrder $α)
          let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
          assumeInstancesCommute
haveI' : e =Q a ^ b := ⟨⟩
          pure (.positive q(zpow_pos $pa $b))
        catch e : Exception =>
          trace[Tactic.positivity.failure] "{e.toMessageData}"
          let sα ← synthInstanceQ q(Semifield $α)
          let oα ← synthInstanceQ q(LinearOrder $α)
          let iα ← synthInstanceQ q(IsStrictOrderedRing $α)
          orElse (← catchNone (ofNonneg q(le_of_lt $pa) sα oα iα))
            (ofNonzero q(ne_of_gt $pa) q(inferInstance))
      | .nonnegative pa =>
        ofNonneg pa (← synthInstanceQ (_ : Q(Type u)))
                    (← synthInstanceQ (_ : Q(Type u))) (← synthInstanceQ (_ : Q(Prop)))
      | .nonzero pa => ofNonzero pa (← synthInstanceQ (_ : Q(Type u)))
      | .none => pure .none

end Mathlib.Meta.Positivity
