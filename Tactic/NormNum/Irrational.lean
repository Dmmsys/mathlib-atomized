/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify

/-! # `norm_num` extension for `Irrational`

This module defines a `norm_num` extension for `Irrational x ^ y` for rational `x` and `y`. It also
supports `Irrational √x` expressions.

## Implementation details
To prove that `(a / b) ^ (p / q)` is irrational, we reduce the problem to showing that `(a / b) ^ p`
is not a `q`-th power of any rational number. This, in turn, reduces to proving that either `a` or
`b` is not a `q`-th power of a natural number, assuming `p` and `q` are coprime.
To show that a given `n : ℕ` is not a `q`-th power, we find a natural number `k`
such that `k ^ q < n < (k + 1) ^ q`, using binary search.

## TODO
Disprove `Irrational x` for rational `x`.

-/

public meta section

namespace Mathlib.Meta

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

section lemmas

/--
theorem `irrational_rpow_rat_of_not_power` / 定理 `irrational_rpow_rat_of_not_power`

English:
theorem irrational_rpow_rat_of_not_power
  statement: {q : Rat} {a b : Nat}
  proof: by
  simp only [Irrational, Rat.cast_div, Rat.cast_natCast, Real.rpow_eq_pow, Set.mem_range,
    not_exists]
  intro x hx
  absurd h x
  rify
  rw [hx]; rw [← Real.rpow_mul_natCast (by simpa)]; rw [div_mul_cancel₀ _ (by simp; lia)]
  simp

中文:
定理 irrational_rpow_rat_of_not_power
  结论: {q : Rat} {a b : 自然数}
  证明: by
  simp only [Irrational, Rat.cast_div, Rat.cast_natCast, Real.rpow_eq_pow, Set.mem_range,
    not_exists]
  intro x hx
  absurd h x
  rify
  rw [hx]; rw [← Real.rpow_mul_natCast (by simpa)]; rw [div_mul_cancel₀ _ (by simp; lia)]
  simp
-/
private theorem irrational_rpow_rat_of_not_power {q : Rat} {a b : Nat}
    (h : forall p : Rat, q ^ a != p ^ b) (hb : 0 < b) (hq : 0 <= q) :
    Irrational (Real.rpow q (a / b : Rat)) := by
  simp only [Irrational, Rat.cast_div, Rat.cast_natCast, Real.rpow_eq_pow, Set.mem_range,
    not_exists]
  intro x hx
  absurd h x
  rify
  rw [hx]; rw [← Real.rpow_mul_natCast (by simpa)]; rw [div_mul_cancel₀ _ (by simp; lia)]
  simp

/--
theorem `not_power_nat_pow` / 定理 `not_power_nat_pow`

English:
theorem not_power_nat_pow
  statement: {n p q : Nat} (h_coprime : p.Coprime q) (hq : 0 < q)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simpa [hq.ne'] using h 0
  contrapose! h
let f := n.factorization.mapRange (· / q) by simp
  suffices hf : n.factorization = q • f by
    have hf0 : f 0 = 0 := by simpa [hq.ne'] using congr($hf 0)
    refine ⟨f.prod (· ^ ·), Nat.factorization_inj hn (by s

中文:
定理 not_power_nat_pow
  结论: {n p q : 自然数} (h_coprime : p.Coprime q) (hq : 0 < q)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simpa [hq.ne'] using h 0
  contrapose! h
let f := n.factorization.mapRange (· / q) by simp
  suffices hf : n.factorization = q • f by
    have hf0 : f 0 = 0 := by simpa [hq.ne'] using congr($hf 0)
    refine ⟨f.prod (· ^ ·), Nat.factorization_inj hn (by s
-/
private theorem not_power_nat_pow {n p q : Nat} (h_coprime : p.Coprime q) (hq : 0 < q)
    (h : forall m, n != m ^ q) (m : Nat) : n ^ p != m ^ q := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simpa [hq.ne'] using h 0
  contrapose! h
let f := n.factorization.mapRange (· / q) by simp
  suffices hf : n.factorization = q • f by
    have hf0 : f 0 = 0 := by simpa [hq.ne'] using congr($hf 0)
    refine ⟨f.prod (· ^ ·), Nat.factorization_inj hn (by simp [hf0]) ?_⟩
    rwa [Nat.factorization_pow, n.factorization_prod_pow_eq_self_of_le_factorization ?_]
    exact hf ▸ le_self_nsmul zero_le (by lia)
  ext z
  rw [Finsupp.smul_apply]; rw [smul_eq_mul]; rw [Finsupp.mapRange_apply]; rw [Nat.mul_div_cancel']
  simpa using h_coprime.symm.dvd_of_dvd_mul_left ⟨_, by simpa using congr(Nat.factorization $h z)⟩

/--
theorem `not_power_nat_of_bounds` / 定理 `not_power_nat_of_bounds`

English:
theorem not_power_nat_of_bounds
  statement: {n k d : Nat}
  proof: by
  intro h
  rw [h] at h_left h_right
  have : k < m := lt_of_pow_lt_pow_left' d h_left
  have : m < k + 1 := lt_of_pow_lt_pow_left' d h_right
  lia

中文:
定理 not_power_nat_of_bounds
  结论: {n k d : 自然数}
  证明: by
  intro h
  rw [h] at h_left h_right
  have : k < m := lt_of_pow_lt_pow_left' d h_left
  have : m < k + 1 := lt_of_pow_lt_pow_left' d h_right
  lia
-/
private theorem not_power_nat_of_bounds {n k d : Nat}
    (h_left : k ^ d < n) (h_right : n < (k + 1) ^ d) {m : Nat} :
    n != m ^ d := by
  intro h
  rw [h] at h_left h_right
  have : k < m := lt_of_pow_lt_pow_left' d h_left
  have : m < k + 1 := lt_of_pow_lt_pow_left' d h_right
  lia

/--
theorem `not_power_nat_pow_of_bounds` / 定理 `not_power_nat_pow_of_bounds`

English:
theorem not_power_nat_pow_of_bounds
  statement: {n k p q : Nat}
  proof: by
  apply not_power_nat_pow h_coprime hq
  intro m
  apply not_power_nat_of_bounds h_left h_right

中文:
定理 not_power_nat_pow_of_bounds
  结论: {n k p q : 自然数}
  证明: by
  apply not_power_nat_pow h_coprime hq
  intro m
  apply not_power_nat_of_bounds h_left h_right
-/
private theorem not_power_nat_pow_of_bounds {n k p q : Nat}
    (hq : 0 < q) (h_coprime : p.Coprime q) (h_left : k ^ q < n) (h_right : n < (k + 1) ^ q)
    (m : Nat) :
    n ^ p != m ^ q := by
  apply not_power_nat_pow h_coprime hq
  intro m
  apply not_power_nat_of_bounds h_left h_right

/--
lemma `eq_of_mul_eq_mul_of_coprime_aux` / 引理 `eq_of_mul_eq_mul_of_coprime_aux`

English:
lemma eq_of_mul_eq_mul_of_coprime_aux
  statement: {a b x y : Nat} (hab : a.Coprime b)
  proof: Nat.Coprime.dvd_of_dvd_mul_left hab (Dvd.intro x h)

中文:
引理 eq_of_mul_eq_mul_of_coprime_aux
  结论: {a b x y : 自然数} (hab : a.Coprime b)
  证明: Nat.Coprime.dvd_of_dvd_mul_left hab (Dvd.intro x h)
-/
private lemma eq_of_mul_eq_mul_of_coprime_aux {a b x y : Nat} (hab : a.Coprime b)
    (h : a * x = b * y) : a ∣ y := Nat.Coprime.dvd_of_dvd_mul_left hab (Dvd.intro x h)

/--
lemma `eq_of_mul_eq_mul_of_coprime` / 引理 `eq_of_mul_eq_mul_of_coprime`

English:
lemma eq_of_mul_eq_mul_of_coprime
  statement: {a b x y : Nat} (hab : a.Coprime b) (hxy : x.Coprime y)
  proof: by
  apply Nat.dvd_antisymm
  · exact eq_of_mul_eq_mul_of_coprime_aux hab h
  · exact eq_of_mul_eq_mul_of_coprime_aux (x := b) hxy.symm (by rw [mul_comm, ← h, mul_comm])

中文:
引理 eq_of_mul_eq_mul_of_coprime
  结论: {a b x y : 自然数} (hab : a.Coprime b) (hxy : x.Coprime y)
  证明: by
  apply Nat.dvd_antisymm
  · exact eq_of_mul_eq_mul_of_coprime_aux hab h
  · exact eq_of_mul_eq_mul_of_coprime_aux (x := b) hxy.symm (by rw [mul_comm, ← h, mul_comm])
-/
private lemma eq_of_mul_eq_mul_of_coprime {a b x y : Nat} (hab : a.Coprime b) (hxy : x.Coprime y)
    (h : a * x = b * y) : a = y := by
  apply Nat.dvd_antisymm
  · exact eq_of_mul_eq_mul_of_coprime_aux hab h
  · exact eq_of_mul_eq_mul_of_coprime_aux (x := b) hxy.symm (by rw [mul_comm, ← h, mul_comm])

/--
theorem `not_power_rat_of_num_aux` / 定理 `not_power_rat_of_num_aux`

English:
theorem not_power_rat_of_num_aux
  statement: {a b d : Nat}
  proof: by
  by_cases hb_zero : b = 0
  · subst hb_zero
    contrapose! ha
    simp only [Nat.coprime_zero_right] at h_coprime
    subst h_coprime
    use 1
    simp
  by_contra! h
  rw [← Rat.num_div_den q] at h
  set x' := q.num
  set y := q.den
  obtain ⟨x, hx'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= x' b

中文:
定理 not_power_rat_of_num_aux
  结论: {a b d : 自然数}
  证明: by
  by_cases hb_zero : b = 0
  · subst hb_zero
    contrapose! ha
    simp only [Nat.coprime_zero_right] at h_coprime
    subst h_coprime
    use 1
    simp
  by_contra! h
  rw [← Rat.num_div_den q] at h
  set x' := q.num
  set y := q.den
  obtain ⟨x, hx'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= x' b
-/
private theorem not_power_rat_of_num_aux {a b d : Nat}
    (h_coprime : a.Coprime b) (ha : forall x, a != x ^ d) {q : Rat} (hq : 0 <= q) :
    (a / b : Rat) != q ^ d := by
  by_cases hb_zero : b = 0
  · subst hb_zero
    contrapose! ha
    simp only [Nat.coprime_zero_right] at h_coprime
    subst h_coprime
    use 1
    simp
  by_contra! h
  rw [← Rat.num_div_den q] at h
  set x' := q.num
  set y := q.den
  obtain ⟨x, hx'⟩ := Int.eq_ofNat_of_zero_le (show 0 <= x' by rwa [Rat.num_nonneg])
  rw [hx'] at h
  specialize ha x
  simp only [Int.cast_natCast, div_pow] at h
  rw [div_eq_div_iff] at h
  rotate_left
  · simpa
  · simp [y]
  replace h : a * y ^ d = x ^ d * b := by
    qify
    assumption
  apply ha
  conv at h => rhs; rw [mul_comm]
  apply eq_of_mul_eq_mul_of_coprime h_coprime _ h
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  simpa [hx'] using (show x'.natAbs.Coprime y from Rat.reduced q)

/--
theorem `not_power_rat_of_num` / 定理 `not_power_rat_of_num`

English:
theorem not_power_rat_of_num
  statement: {a b d : Nat}
  proof: by
  by_cases hq : 0 <= q
  · apply not_power_rat_of_num_aux h_coprime ha hq
  rcases d.even_or_odd with (h_even | h_odd)
  · have := not_power_rat_of_num_aux h_coprime (q := -q) ha (by linarith)
    rwa [h_even.neg_pow] at this
  · contrapose hq
    rw [← h_odd.pow_nonneg_iff]; rw [← hq]
    positi

中文:
定理 not_power_rat_of_num
  结论: {a b d : 自然数}
  证明: by
  by_cases hq : 0 <= q
  · apply not_power_rat_of_num_aux h_coprime ha hq
  rcases d.even_or_odd with (h_even | h_odd)
  · have := not_power_rat_of_num_aux h_coprime (q := -q) ha (by linarith)
    rwa [h_even.neg_pow] at this
  · contrapose hq
    rw [← h_odd.pow_nonneg_iff]; rw [← hq]
    positi
-/
private theorem not_power_rat_of_num {a b d : Nat}
    (h_coprime : a.Coprime b) (ha : forall x, a != x ^ d) (q : Rat) :
    (a / b : Rat) != q ^ d := by
  by_cases hq : 0 <= q
  · apply not_power_rat_of_num_aux h_coprime ha hq
  rcases d.even_or_odd with (h_even | h_odd)
  · have := not_power_rat_of_num_aux h_coprime (q := -q) ha (by linarith)
    rwa [h_even.neg_pow] at this
  · contrapose hq
    rw [← h_odd.pow_nonneg_iff]; rw [← hq]
    positivity

/--
theorem `irrational_rpow_rat_rat_of_num` / 定理 `irrational_rpow_rat_rat_of_num`

English:
theorem irrational_rpow_rat_rat_of_num
  statement: {x y : Real} {x_num x_den y_num y_den k_num : Nat}
  proof: by
  have hy_den_pos : 0 < y_den := by
    by_contra! h
    simp only [nonpos_iff_eq_zero] at h
    simp only [h, pow_zero, Nat.lt_one_iff] at hn1 hn2
    lia
  rcases hx_isNNRat with ⟨hx_inv, hx_eq⟩
  rcases hy_isNNRat with ⟨hy_inv, hy_eq⟩
  rw [hy_eq]; rw [hx_eq]
  have h1 : (y_num * ⅟(y_den : Rea

中文:
定理 irrational_rpow_rat_rat_of_num
  结论: {x y : 实数} {x_num x_den y_num y_den k_num : 自然数}
  证明: by
  have hy_den_pos : 0 < y_den := by
    by_contra! h
    simp only [nonpos_iff_eq_zero] at h
    simp only [h, pow_zero, Nat.lt_one_iff] at hn1 hn2
    lia
  rcases hx_isNNRat with ⟨hx_inv, hx_eq⟩
  rcases hy_isNNRat with ⟨hy_inv, hy_eq⟩
  rw [hy_eq]; rw [hx_eq]
  have h1 : (y_num * ⅟(y_den : Rea

Depends on / 依赖: Nat.lt_one_iff, hx_eq, hx_inv, hx_isNNRat, hy_den_pos, hy_eq, hy_inv, hy_isNNRat, irrational_rpow_rat_of_not_power, lt_one_iff, nonpos_iff_eq_zero, pow_zero, x_den, x_num, y_den, y_num
-/
theorem irrational_rpow_rat_rat_of_num {x y : Real} {x_num x_den y_num y_den k_num : Nat}
    (hx_isNNRat : IsNNRat x x_num x_den)
    (hy_isNNRat : IsNNRat y y_num y_den)
    (hx_coprime : Nat.Coprime x_num x_den)
    (hy_coprime : Nat.Coprime y_num y_den)
    (hn1 : k_num ^ y_den < x_num)
    (hn2 : x_num < (k_num + 1) ^ y_den) :
    Irrational (x ^ y) := by
  have hy_den_pos : 0 < y_den := by
    by_contra! h
    simp only [nonpos_iff_eq_zero] at h
    simp only [h, pow_zero, Nat.lt_one_iff] at hn1 hn2
    lia
  rcases hx_isNNRat with ⟨hx_inv, hx_eq⟩
  rcases hy_isNNRat with ⟨hy_inv, hy_eq⟩
  rw [hy_eq]; rw [hx_eq]
  have h1 : (y_num * ⅟(y_den : Real) : Real) = ((y_num / y_den : Rat) : Real) := by
    simp
    rfl
  have h2 : (x_num * ⅟(x_den : Real) : Real) = ((x_num / x_den : Rat) : Real) := by
    simp
    rfl
  rw [h1]; rw [h2]
  refine irrational_rpow_rat_of_not_power ?_ hy_den_pos ?_
  · simp only [div_pow, ← Nat.cast_pow]
    apply not_power_rat_of_num
    · apply Nat.Coprime.pow _ _ hx_coprime
    · apply not_power_nat_pow_of_bounds hy_den_pos hy_coprime hn1 hn2
  · positivity

/--
theorem `irrational_rpow_rat_rat_of_den` / 定理 `irrational_rpow_rat_rat_of_den`

English:
theorem irrational_rpow_rat_rat_of_den
  statement: {x y : Real} {x_num x_den y_num y_den k_den : Nat}
  proof: by
  rcases hx_isNNRat with ⟨hx_inv, hx_eq⟩
  apply Irrational.of_inv
  rw [← Real.inv_rpow (by simp only [hx_eq]; rw [invOf_eq_inv]; positivity)]
  apply irrational_rpow_rat_rat_of_num (x_num := x_den) (x_den := x_num) _ hy_isNNRat
    (Nat.coprime_comm.mp hx_coprime) hy_coprime hd1 hd2
  refine ⟨i

中文:
定理 irrational_rpow_rat_rat_of_den
  结论: {x y : 实数} {x_num x_den y_num y_den k_den : 自然数}
  证明: by
  rcases hx_isNNRat with ⟨hx_inv, hx_eq⟩
  apply Irrational.of_inv
  rw [← Real.inv_rpow (by simp only [hx_eq]; rw [invOf_eq_inv]; positivity)]
  apply irrational_rpow_rat_rat_of_num (x_num := x_den) (x_den := x_num) _ hy_isNNRat
    (Nat.coprime_comm.mp hx_coprime) hy_coprime hd1 hd2
  refine ⟨i

Depends on / 依赖: Irrational, Irrational.of_inv, Nat.coprime_comm.mp, Real.inv_rpow, coprime_comm, hx_coprime, hx_eq, hx_inv, hx_isNNRat, hy_coprime, hy_isNNRat, invOf_eq_inv, inv_rpow, invertibleOfNonzero, irrational_rpow_rat_rat_of_num, of_inv, x_den, x_num
-/
theorem irrational_rpow_rat_rat_of_den {x y : Real} {x_num x_den y_num y_den k_den : Nat}
    (hx_isNNRat : IsNNRat x x_num x_den)
    (hy_isNNRat : IsNNRat y y_num y_den)
    (hx_coprime : Nat.Coprime x_num x_den)
    (hy_coprime : Nat.Coprime y_num y_den)
    (hd1 : k_den ^ y_den < x_den)
    (hd2 : x_den < (k_den + 1) ^ y_den) :
    Irrational (x ^ y) := by
  rcases hx_isNNRat with ⟨hx_inv, hx_eq⟩
  apply Irrational.of_inv
  rw [← Real.inv_rpow (by simp only [hx_eq]; rw [invOf_eq_inv]; positivity)]
  apply irrational_rpow_rat_rat_of_num (x_num := x_den) (x_den := x_num) _ hy_isNNRat
    (Nat.coprime_comm.mp hx_coprime) hy_coprime hd1 hd2
  refine ⟨invertibleOfNonzero (fun _ => ?_), by simp [hx_eq]⟩
  simp_all

/--
theorem `irrational_rpow_nat_rat` / 定理 `irrational_rpow_nat_rat`

English:
theorem irrational_rpow_nat_rat
  statement: {x y : Real} {x_num y_num y_den k : Nat}
  proof: irrational_rpow_rat_rat_of_num hx_isNat.to_isNNRat hy_isNNRat (by simp) hy_coprime hn1 hn2

中文:
定理 irrational_rpow_nat_rat
  结论: {x y : 实数} {x_num y_num y_den k : 自然数}
  证明: irrational_rpow_rat_rat_of_num hx_isNat.to_isNNRat hy_isNNRat (by simp) hy_coprime hn1 hn2

Depends on / 依赖: hx_isNat, hx_isNat.to_isNNRat, hy_coprime, hy_isNNRat, irrational_rpow_rat_rat_of_num, to_isNNRat
-/
theorem irrational_rpow_nat_rat {x y : Real} {x_num y_num y_den k : Nat}
    (hx_isNat : IsNat x x_num)
    (hy_isNNRat : IsNNRat y y_num y_den)
    (hy_coprime : Nat.Coprime y_num y_den)
    (hn1 : k ^ y_den < x_num)
    (hn2 : x_num < (k + 1) ^ y_den) :
    Irrational (x ^ y) :=
  irrational_rpow_rat_rat_of_num hx_isNat.to_isNNRat hy_isNNRat (by simp) hy_coprime hn1 hn2

/--
theorem `irrational_sqrt_rat_of_num` / 定理 `irrational_sqrt_rat_of_num`

English:
theorem irrational_sqrt_rat_of_num
  statement: {x : Real} {num den num_k : Nat}
  proof: by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_num hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hn1 hn2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

中文:
定理 irrational_sqrt_rat_of_num
  结论: {x : 实数} {num den num_k : 自然数}
  证明: by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_num hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hn1 hn2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

Depends on / 依赖: Invertible, Invertible.mk, Real.sqrt_eq_rpow, hx_coprime, hx_isNNRat, irrational_rpow_rat_rat_of_num, sqrt_eq_rpow, y_den, y_num
-/
theorem irrational_sqrt_rat_of_num {x : Real} {num den num_k : Nat}
    (hx_isNNRat : IsNNRat x num den)
    (hx_coprime : Nat.Coprime num den)
    (hn1 : num_k ^ 2 < num)
    (hn2 : num < (num_k + 1) ^ 2) :
    Irrational (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_num hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hn1 hn2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

/--
theorem `irrational_sqrt_rat_of_den` / 定理 `irrational_sqrt_rat_of_den`

English:
theorem irrational_sqrt_rat_of_den
  statement: {x : Real} {num den den_k : Nat}
  proof: by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_den hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hd1 hd2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

中文:
定理 irrational_sqrt_rat_of_den
  结论: {x : 实数} {num den den_k : 自然数}
  证明: by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_den hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hd1 hd2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

Depends on / 依赖: Invertible, Invertible.mk, Real.sqrt_eq_rpow, hx_coprime, hx_isNNRat, irrational_rpow_rat_rat_of_den, sqrt_eq_rpow, y_den, y_num
-/
theorem irrational_sqrt_rat_of_den {x : Real} {num den den_k : Nat}
    (hx_isNNRat : IsNNRat x num den)
    (hx_coprime : Nat.Coprime num den)
    (hd1 : den_k ^ 2 < den)
    (hd2 : den < (den_k + 1) ^ 2) :
    Irrational (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_den hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hd1 hd2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

/--
theorem `irrational_sqrt_nat` / 定理 `irrational_sqrt_nat`

English:
theorem irrational_sqrt_nat
  statement: {x : Real} {n k : Nat}
  proof: irrational_sqrt_rat_of_num hx_isNat.to_isNNRat (by simp) hn1 hn2

中文:
定理 irrational_sqrt_nat
  结论: {x : 实数} {n k : 自然数}
  证明: irrational_sqrt_rat_of_num hx_isNat.to_isNNRat (by simp) hn1 hn2

Depends on / 依赖: hx_isNat, hx_isNat.to_isNNRat, irrational_sqrt_rat_of_num, to_isNNRat
-/
theorem irrational_sqrt_nat {x : Real} {n k : Nat}
    (hx_isNat : IsNat x n)
    (hn1 : k ^ 2 < n)
    (hn2 : n < (k + 1) ^ 2) :
    Irrational (Real.sqrt x) :=
  irrational_sqrt_rat_of_num hx_isNat.to_isNNRat (by simp) hn1 hn2

end lemmas

/--
Definition of `NotPowerCertificate` / `NotPowerCertificate` 的定义

English:
structure NotPowerCertificate
  parameters: (m n : Q(Nat))
  axioms and operations (3):
    - k : Q(Nat)
    - pf_left : Q($k ^ $n < $m)
    - pf_right : Q($m < ($k + 1) ^ $n)

中文:
结构 NotPowerCertificate
  参数: (m n : Q(自然数))
  公理与运算 (3 个):
    - k : Q(自然数)
    - pf_left : Q($k ^ $n < $m)
    - pf_right : Q($m < ($k + 1) ^ $n)
-/
structure NotPowerCertificate (m n : Q(Nat)) where
  /-- Natural `k` such that `k ^ n < m < (k + 1) ^ n`. -/
  k : Q(Nat)
  /-- Proof of `k ^ n < m`. -/
  pf_left : Q($k ^ $n < $m)
  /-- Proof of `m < (k + 1) ^ n`. -/
  pf_right : Q($m < ($k + 1) ^ $n)

/--
Definition of `findNotPowerCertificateCore` / `findNotPowerCertificateCore` 的定义

English:
definition findNotPowerCertificateCore
  signature: (m n : Nat)
  body: Id.run do
  let mut left := 0
  let mut right := m + 1
  while right - left > 1 do
    let middle := (left + right) / 2
    if middle ^ n <= m then
      left := middle
    else
      right := middle
  if left ^ n < m then
    return some left
  return none

中文:
定义 findNotPowerCertificateCore
  签名: (m n : 自然数)
  定义体: Id.run do
  let mut left := 0
  let mut right := m + 1
  while right - left > 1 do
    let middle := (left + right) / 2
    if middle ^ n <= m then
      left := middle
    else
      right := middle
  if left ^ n < m then
    return some left
  return none

Depends on / 依赖: Id.run
-/
def findNotPowerCertificateCore (m n : Nat) : Option Nat := Id.run do
  let mut left := 0
  let mut right := m + 1
  while right - left > 1 do
    let middle := (left + right) / 2
    if middle ^ n <= m then
      left := middle
    else
      right := middle
  if left ^ n < m then
    return some left
  return none

/--
Definition of `findNotPowerCertificate` / `findNotPowerCertificate` 的定义

English:
definition findNotPowerCertificate
  signature: (m n : Q(Nat))
  body: do
  let .isNat (_ : Q(AddMonoidWithOne Nat)) m _ ← derive m | failure
  let .isNat (_ : Q(AddMonoidWithOne Nat)) n _ ← derive n | failure
  let mVal := m.natLit!
  let nVal := n.natLit!
  let some k := findNotPowerCertificateCore mVal nVal | failure
  let .isBool true pf_left ← derive q($k ^ $n < $

中文:
定义 findNotPowerCertificate
  签名: (m n : Q(自然数))
  定义体: do
  let .isNat (_ : Q(AddMonoidWithOne Nat)) m _ ← derive m | failure
  let .isNat (_ : Q(AddMonoidWithOne Nat)) n _ ← derive n | failure
  let mVal := m.natLit!
  let nVal := n.natLit!
  let some k := findNotPowerCertificateCore mVal nVal | failure
  let .isBool true pf_left ← derive q($k ^ $n < $
-/
def findNotPowerCertificate (m n : Q(Nat)) : MetaM (NotPowerCertificate m n) := do
  let .isNat (_ : Q(AddMonoidWithOne Nat)) m _ ← derive m | failure
  let .isNat (_ : Q(AddMonoidWithOne Nat)) n _ ← derive n | failure
  let mVal := m.natLit!
  let nVal := n.natLit!
  let some k := findNotPowerCertificateCore mVal nVal | failure
  let .isBool true pf_left ← derive q($k ^ $n < $m) | failure
  let .isBool true pf_right ← derive q($m < ($k + 1) ^ $n) | failure
  return ⟨q($k), pf_left, pf_right⟩

/-- `norm_num` extension that proves `Irrational x ^ y` for rational `y`. `x` may be
natural or rational. -/
@[norm_num Irrational (_ ^ (_ : Real))]
/--
Definition of `evalIrrationalRpow` / `evalIrrationalRpow` 的定义

English:
definition evalIrrationalRpow
  signature: : NormNumExt where eval {u α} e
  body: match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (($x : Real) ^ ($y : Real))) => do
    let .isNNRat sReal _ y_num y_den y_isNNRat ← derive y | failure
    let ⟨gy, hy_coprime⟩ := proveNatGCD y_num y_den
    if gy.natLit! != 1 then failure
let _ : gy =Q 1 := ⟨⟩
    match ← derive x with
    | .isNa

中文:
定义 evalIrrationalRpow
  签名: : NormNumExt where eval {u α} e
  定义体: match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (($x : Real) ^ ($y : Real))) => do
    let .isNNRat sReal _ y_num y_den y_isNNRat ← derive y | failure
    let ⟨gy, hy_coprime⟩ := proveNatGCD y_num y_den
    if gy.natLit! != 1 then failure
let _ : gy =Q 1 := ⟨⟩
    match ← derive x with
    | .isNa

Depends on / 依赖: Irrational, assumeInstancesCommute, cert.pf_left, cert.pf_right, derive, failure, findNotPowerCertificate, gy.natLit, hy_coprime, irrational_rpow_nat_rat, isNNRat, isTrue, natLit, pf_left, pf_right, proveNatGCD, return, x_isNat, x_num, y_den
-/
def evalIrrationalRpow : NormNumExt where eval {u α} e :=
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (($x : Real) ^ ($y : Real))) => do
    let .isNNRat sReal _ y_num y_den y_isNNRat ← derive y | failure
    let ⟨gy, hy_coprime⟩ := proveNatGCD y_num y_den
    if gy.natLit! != 1 then failure
let _ : gy =Q 1 := ⟨⟩
    match ← derive x with
    | .isNat sReal ex x_isNat =>
      let cert ← findNotPowerCertificate q($ex) y_den
      assumeInstancesCommute
      return .isTrue q(irrational_rpow_nat_rat $x_isNat $y_isNNRat $hy_coprime
 cert.pf_left cert.pf_right)
    | .isNNRat sReal _ x_num x_den x_isNNRat =>
      let ⟨gx, hx_coprime⟩ := proveNatGCD x_num x_den
      if gx.natLit! != 1 then failure
let _ : gx =Q 1 := ⟨⟩
      let hx_isNNRat' : Q(IsNNRat $x $x_num $x_den) := x_isNNRat
      let hy_isNNRat' : Q(IsNNRat $y $y_num $y_den) := y_isNNRat
      try
        let numCert ← findNotPowerCertificate q($x_num) y_den
        assumeInstancesCommute
        return Result.isTrue q(irrational_rpow_rat_rat_of_num $hx_isNNRat' $hy_isNNRat'
 hx_coprime hy_coprime numCert.pf_left numCert.pf_right)
      catch _ =>
        let denCert ← findNotPowerCertificate q($x_den) y_den
        assumeInstancesCommute
        return Result.isTrue q(irrational_rpow_rat_rat_of_den $hx_isNNRat' $hy_isNNRat'
 hx_coprime hy_coprime denCert.pf_left denCert.pf_right)
    | _ => failure
  | _, _, _ => failure

/-- `norm_num` extension that proves `Irrational √x` for rational `x`. -/
@[norm_num Irrational (Real.sqrt _)]
/--
Definition of `evalIrrationalSqrt` / `evalIrrationalSqrt` 的定义

English:
definition evalIrrationalSqrt
  signature: : NormNumExt where eval {u α} e
  body: do
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (√$x)) => do
    match ← derive x with
    | .isNat sReal ex pf =>
      let cert ← findNotPowerCertificate ex q(nat_lit 2)
      assumeInstancesCommute
      return .isTrue q(irrational_sqrt_nat $pf $cert.pf_left $cert.pf_right)
    | .isNNRat 

中文:
定义 evalIrrationalSqrt
  签名: : NormNumExt where eval {u α} e
  定义体: do
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (√$x)) => do
    match ← derive x with
    | .isNat sReal ex pf =>
      let cert ← findNotPowerCertificate ex q(nat_lit 2)
      assumeInstancesCommute
      return .isTrue q(irrational_sqrt_nat $pf $cert.pf_left $cert.pf_right)
    | .isNNRat 
-/
def evalIrrationalSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (√$x)) => do
    match ← derive x with
    | .isNat sReal ex pf =>
      let cert ← findNotPowerCertificate ex q(nat_lit 2)
      assumeInstancesCommute
      return .isTrue q(irrational_sqrt_nat $pf $cert.pf_left $cert.pf_right)
    | .isNNRat sReal eq en ed pf =>
      let ⟨g, pf_coprime⟩ := proveNatGCD en ed
      if g.natLit! != 1 then failure
let _ : g =Q 1 := ⟨⟩
      try
        let numCert ← findNotPowerCertificate en q(nat_lit 2)
        assumeInstancesCommute
        return Result.isTrue
          q(irrational_sqrt_rat_of_num $pf $pf_coprime $numCert.pf_left $numCert.pf_right)
      catch _ =>
        let denCert ← findNotPowerCertificate ed q(nat_lit 2)
        assumeInstancesCommute
        return Result.isTrue
          q(irrational_sqrt_rat_of_den $pf $pf_coprime $denCert.pf_left $denCert.pf_right)
    | _ => failure
  | _, _, _ => failure

end NormNum

end Mathlib.Meta
