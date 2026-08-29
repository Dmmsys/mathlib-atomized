/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha, Thomas Browning
-/
module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic.Positivity

/-!

The nth Harmonic number is not an integer. We formalize the proof using
2-adic valuations. This proof is due to Kürschák.

Reference:
https://kconrad.math.uconn.edu/blurbs/gradnumthy/padicharmonicsum.pdf

-/

public section

/--
lemma `harmonic_pos` / 引理 `harmonic_pos`

English:
lemma harmonic_pos
  given: {n : Nat} (Hn : n != 0)
  statement: 0 < harmonic n
  proof: by
  unfold harmonic
  rw [← Finset.nonempty_range_iff] at Hn
  positivity

中文:
引理 harmonic_pos
  条件: {n : 自然数} (Hn : n != 0)
  结论: 0 < harmonic n
  证明: by
  unfold harmonic
  rw [← Finset.nonempty_range_iff] at Hn
  positivity

Depends on / 依赖: Finset, Finset.nonempty_range_iff, harmonic, nonempty_range_iff
-/
lemma harmonic_pos {n : Nat} (Hn : n != 0) : 0 < harmonic n := by
  unfold harmonic
  rw [← Finset.nonempty_range_iff] at Hn
  positivity

/--
theorem `padicValRat_two_harmonic` / 定理 `padicValRat_two_harmonic`

English:
theorem padicValRat_two_harmonic
  given: (n : Nat)
  statement: padicValRat 2 (harmonic n) = -Nat.log 2 n
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [harmonic_succ]
    have key : padicValRat 2 (harmonic n) != padicValRat 2 (↑(n + 1))⁻¹ := by
      rw [ih]; rw [padicValRat.inv]; rw [padicValRat.of_nat]; rw [Ne]; rw [neg_inj]; rw [Nat.cast_inj]
      exact Nat.log_ne_padicValNat_succ hn
    rw [padicValRat.add_eq_min (harmonic_succ n ▸ (harmonic_pos n.succ_ne_zero).ne')
        (harmonic_pos hn).ne' (inv_ne_zero (Nat.cast_ne_zero.mpr n.succ_ne_zero)) key]; rw [ih]; rw [padicValRat.inv]; rw [padicValRat.of_nat]; rw [min_neg_neg]; rw [neg_inj]; rw [← Nat.cast_max]; rw [Nat.cast_inj]
    exact Nat.max_log_padicValNat_succ_eq_log_succ n

中文:
定理 padicValRat_two_harmonic
  条件: (n : 自然数)
  结论: padicValRat 2 (harmonic n) = -自然数.log 2 n
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [harmonic_succ]
    have key : padicValRat 2 (harmonic n) != padicValRat 2 (↑(n + 1))⁻¹ := by
      rw [ih]; rw [padicValRat.inv]; rw [padicValRat.of_nat]; rw [Ne]; rw [neg_inj]; rw [Nat.cast_inj]
      exact Nat.log_ne_padicValNat_succ hn
    rw [padicValRat.add_eq_min (harmonic_succ n ▸ (harmonic_pos n.succ_ne_zero).ne')
        (harmonic_pos hn).ne' (inv_ne_zero (Nat.cast_ne_zero.mpr n.succ_ne_zero)) key]; rw [ih]; rw [padicValRat.inv]; rw [padicValRat.of_nat]; rw [min_neg_neg]; rw [neg_inj]; rw [← Nat.cast_max]; rw [Nat.cast_inj]
    exact Nat.max_log_padicValNat_succ_eq_log_succ n

Depends on / 依赖: Nat.cast_inj, Nat.cast_ne_zero.mpr, Nat.log_ne_padicValNat_succ, add_eq_min, cast_inj, cast_ne_zero, eq_or_ne, harmonic, harmonic_pos, harmonic_succ, inv_ne_zero, log_ne_padicValNat_succ, n.succ_ne_zero, neg_inj, of_nat, padicVal, padicValRat, padicValRat.add_eq_min, padicValRat.inv, padicValRat.of_nat
-/
theorem padicValRat_two_harmonic (n : Nat) : padicValRat 2 (harmonic n) = -Nat.log 2 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [harmonic_succ]
    have key : padicValRat 2 (harmonic n) != padicValRat 2 (↑(n + 1))⁻¹ := by
      rw [ih]; rw [padicValRat.inv]; rw [padicValRat.of_nat]; rw [Ne]; rw [neg_inj]; rw [Nat.cast_inj]
      exact Nat.log_ne_padicValNat_succ hn
    rw [padicValRat.add_eq_min (harmonic_succ n ▸ (harmonic_pos n.succ_ne_zero).ne')
        (harmonic_pos hn).ne' (inv_ne_zero (Nat.cast_ne_zero.mpr n.succ_ne_zero)) key]; rw [ih]; rw [padicValRat.inv]; rw [padicValRat.of_nat]; rw [min_neg_neg]; rw [neg_inj]; rw [← Nat.cast_max]; rw [Nat.cast_inj]
    exact Nat.max_log_padicValNat_succ_eq_log_succ n

/--
lemma `padicNorm_two_harmonic` / 引理 `padicNorm_two_harmonic`

English:
lemma padicNorm_two_harmonic
  given: {n : Nat} (hn : n != 0)
  proof: by
  rw [Padic.eq_padicNorm]; rw [padicNorm.eq_zpow_of_nonzero (harmonic_pos hn).ne']; rw [padicValRat_two_harmonic]; rw [neg_neg]; rw [zpow_natCast]; rw [Rat.cast_pow]; rw [Rat.cast_natCast]; rw [Nat.cast_ofNat]

中文:
引理 padicNorm_two_harmonic
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  rw [Padic.eq_padicNorm]; rw [padicNorm.eq_zpow_of_nonzero (harmonic_pos hn).ne']; rw [padicValRat_two_harmonic]; rw [neg_neg]; rw [zpow_natCast]; rw [Rat.cast_pow]; rw [Rat.cast_natCast]; rw [Nat.cast_ofNat]

Depends on / 依赖: Nat.cast_ofNat, Padic.eq_padicNorm, Rat.cast_natCast, Rat.cast_pow, cast_natCast, cast_ofNat, cast_pow, eq_padicNorm, eq_zpow_of_nonzero, harmonic_pos, neg_neg, padicNorm, padicNorm.eq_zpow_of_nonzero, padicValRat_two_harmonic, zpow_natCast
-/
lemma padicNorm_two_harmonic {n : Nat} (hn : n != 0) :
    ‖(harmonic n : Rat_[2])‖ = 2 ^ (Nat.log 2 n) := by
  rw [Padic.eq_padicNorm]; rw [padicNorm.eq_zpow_of_nonzero (harmonic_pos hn).ne']; rw [padicValRat_two_harmonic]; rw [neg_neg]; rw [zpow_natCast]; rw [Rat.cast_pow]; rw [Rat.cast_natCast]; rw [Nat.cast_ofNat]

/--
theorem `harmonic_not_int` / 定理 `harmonic_not_int`

English:
theorem harmonic_not_int
  given: {n : Nat} (h : 2 <= n)
  statement: ¬ (harmonic n).isInt
  proof: by
  apply padicNorm.not_int_of_not_padic_int 2
  rw [padicNorm.eq_zpow_of_nonzero (harmonic_pos (ne_zero_of_lt h)).ne']; rw [padicValRat_two_harmonic]; rw [neg_neg]; rw [zpow_natCast]
  exact one_lt_pow₀ one_lt_two (Nat.log_pos one_lt_two h).ne'

中文:
定理 harmonic_not_int
  条件: {n : 自然数} (h : 2 <= n)
  结论: ¬ (harmonic n).is整数
  证明: by
  apply padicNorm.not_int_of_not_padic_int 2
  rw [padicNorm.eq_zpow_of_nonzero (harmonic_pos (ne_zero_of_lt h)).ne']; rw [padicValRat_two_harmonic]; rw [neg_neg]; rw [zpow_natCast]
  exact one_lt_pow₀ one_lt_two (Nat.log_pos one_lt_two h).ne'

Depends on / 依赖: Nat.log_pos, eq_zpow_of_nonzero, harmonic_pos, log_pos, ne_zero_of_lt, neg_neg, not_int_of_not_padic_int, one_lt_two, padicNorm, padicNorm.eq_zpow_of_nonzero, padicNorm.not_int_of_not_padic_int, padicValRat_two_harmonic, zpow_natCast
-/
theorem harmonic_not_int {n : Nat} (h : 2 <= n) : ¬ (harmonic n).isInt := by
  apply padicNorm.not_int_of_not_padic_int 2
  rw [padicNorm.eq_zpow_of_nonzero (harmonic_pos (ne_zero_of_lt h)).ne']; rw [padicValRat_two_harmonic]; rw [neg_neg]; rw [zpow_natCast]
  exact one_lt_pow₀ one_lt_two (Nat.log_pos one_lt_two h).ne'
