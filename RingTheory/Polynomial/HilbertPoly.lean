/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Hilbert polynomials

In this file, we formalise the following statement: if `F` is a field with characteristic `0`, then
given any `p : F[X]` and `d : ℕ`, there exists some `h : F[X]` such that for any large enough
`n : ℕ`, `h(n)` is equal to the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
This `h` is unique and is denoted as `Polynomial.hilbertPoly p d`.

For example, given `d : ℕ`, the power series expansion of `1/(1 - X)ᵈ⁺¹` in `F[X]`
is `Σₙ ((d + n).choose d)Xⁿ`, which equals `Σₙ ((n + 1)···(n + d)/d!)Xⁿ` and hence
`Polynomial.hilbertPoly (1 : F[X]) (d + 1)` is the polynomial `(X + 1)···(X + d)/d!`. Note that
if `d! = 0` in `F`, then the polynomial `(X + 1)···(X + d)/d!` no longer works, so we do not want
`d!` to be divisible by the characteristic of `F`. As `Polynomial.hilbertPoly` may take any
`p : F[X]` and `d : ℕ` as its inputs, it is necessary for us to assume that `CharZero F`.

## Main definitions

* `Polynomial.hilbertPoly p d`. Given a field `F`, a polynomial `p : F[X]` and a natural number `d`,
  if `F` is of characteristic `0`, then `Polynomial.hilbertPoly p d : F[X]` is the polynomial whose
  value at `n` equals the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.

## TODO

* Hilbert polynomials of finitely generated graded modules over Noetherian rings.
-/

@[expose] public section

open Nat PowerSeries

variable (F : Type*) [Field F]

namespace Polynomial

/--
Definition of `preHilbertPoly` / `preHilbertPoly` 的定义

English:
definition preHilbertPoly
  signature: (d k : Nat)
  body: (d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1))

中文:
定义 preHilbertPoly
  签名: (d k : 自然数)
  定义体: (d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1))

Depends on / 依赖: Polynomial, Polynomial.X, ascPochhammer, d.factorial, factorial
-/
noncomputable def preHilbertPoly (d k : Nat) : F[X] :=
  (d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1))

/--
lemma `natDegree_preHilbertPoly` / 引理 `natDegree_preHilbertPoly`

English:
lemma natDegree_preHilbertPoly
  given: [CharZero F] (d k : Nat)
  proof: by
  have hne : (d ! : F) != 0 := by norm_cast; positivity
  rw [preHilbertPoly]; rw [natDegree_smul _ (inv_ne_zero hne)]; rw [natDegree_comp]; rw [ascPochhammer_natDegree]; rw [add_comm_sub]; rw [← C_1]; rw [← map_sub]; rw [natDegree_add_C]; rw [natDegree_X]; rw [mul_one]

中文:
引理 natDegree_preHilbertPoly
  条件: [CharZero F] (d k : 自然数)
  证明: by
  have hne : (d ! : F) != 0 := by norm_cast; positivity
  rw [preHilbertPoly]; rw [natDegree_smul _ (inv_ne_zero hne)]; rw [natDegree_comp]; rw [ascPochhammer_natDegree]; rw [add_comm_sub]; rw [← C_1]; rw [← map_sub]; rw [natDegree_add_C]; rw [natDegree_X]; rw [mul_one]

Depends on / 依赖: add_comm_sub, ascPochhammer_natDegree, inv_ne_zero, map_sub, mul_one, natDegree_X, natDegree_add_C, natDegree_comp, natDegree_smul, preHilbertPoly
-/
lemma natDegree_preHilbertPoly [CharZero F] (d k : Nat) :
    (preHilbertPoly F d k).natDegree = d := by
  have hne : (d ! : F) != 0 := by norm_cast; positivity
  rw [preHilbertPoly]; rw [natDegree_smul _ (inv_ne_zero hne)]; rw [natDegree_comp]; rw [ascPochhammer_natDegree]; rw [add_comm_sub]; rw [← C_1]; rw [← map_sub]; rw [natDegree_add_C]; rw [natDegree_X]; rw [mul_one]

/--
lemma `coeff_preHilbertPoly_self` / 引理 `coeff_preHilbertPoly_self`

English:
lemma coeff_preHilbertPoly_self
  given: [CharZero F] (d k : Nat)
  proof: by
  delta preHilbertPoly
  have hne : (d ! : F) != 0 := by norm_cast; positivity
  have heq : d = ((ascPochhammer F d).comp (X - C (k : F) + 1)).natDegree :=
    (natDegree_preHilbertPoly F d k).symm.trans (natDegree_smul _ (inv_ne_zero hne))
  nth_rw 3 [heq]
  calc
  _ = (d ! : F)⁻¹ • ((ascPochham

中文:
引理 coeff_preHilbertPoly_self
  条件: [CharZero F] (d k : 自然数)
  证明: by
  delta preHilbertPoly
  have hne : (d ! : F) != 0 := by norm_cast; positivity
  have heq : d = ((ascPochhammer F d).comp (X - C (k : F) + 1)).natDegree :=
    (natDegree_preHilbertPoly F d k).symm.trans (natDegree_smul _ (inv_ne_zero hne))
  nth_rw 3 [heq]
  calc
  _ = (d ! : F)⁻¹ • ((ascPochham

Depends on / 依赖: ascPochhammer, coeff_natDegree, coeff_smul, inv_ne_zero, leadingCoeff, leadingCoeff_comp, map_sub, natDegree, natDegree_X_sub_C, natDegree_preHilbertPoly, natDegree_smul, ne_of_eq_of_ne, nth_rw, one_, preHilbertPoly, sub_add, symm.trans
-/
lemma coeff_preHilbertPoly_self [CharZero F] (d k : Nat) :
    (preHilbertPoly F d k).coeff d = (d ! : F)⁻¹ := by
  delta preHilbertPoly
  have hne : (d ! : F) != 0 := by norm_cast; positivity
  have heq : d = ((ascPochhammer F d).comp (X - C (k : F) + 1)).natDegree :=
    (natDegree_preHilbertPoly F d k).symm.trans (natDegree_smul _ (inv_ne_zero hne))
  nth_rw 3 [heq]
  calc
  _ = (d ! : F)⁻¹ • ((ascPochhammer F d).comp (X - C ((k : F) - 1))).leadingCoeff := by
    simp only [sub_add, ← C_1, ← map_sub, coeff_smul, coeff_natDegree]
  _ = (d ! : F)⁻¹ := by
    simp only [leadingCoeff_comp (ne_of_eq_of_ne (natDegree_X_sub_C _) one_ne_zero), Monic.def.1
      (monic_ascPochhammer _ _), leadingCoeff_X_sub_C, one_pow, smul_eq_mul, mul_one]

/--
lemma `leadingCoeff_preHilbertPoly` / 引理 `leadingCoeff_preHilbertPoly`

English:
lemma leadingCoeff_preHilbertPoly
  given: [CharZero F] (d k : Nat)
  proof: by
  rw [leadingCoeff]; rw [natDegree_preHilbertPoly]; rw [coeff_preHilbertPoly_self]

中文:
引理 leadingCoeff_preHilbertPoly
  条件: [CharZero F] (d k : 自然数)
  证明: by
  rw [leadingCoeff]; rw [natDegree_preHilbertPoly]; rw [coeff_preHilbertPoly_self]

Depends on / 依赖: coeff_preHilbertPoly_self, leadingCoeff, natDegree_preHilbertPoly
-/
lemma leadingCoeff_preHilbertPoly [CharZero F] (d k : Nat) :
    (preHilbertPoly F d k).leadingCoeff = (d ! : F)⁻¹ := by
  rw [leadingCoeff]; rw [natDegree_preHilbertPoly]; rw [coeff_preHilbertPoly_self]

/--
lemma `preHilbertPoly_eq_choose_sub_add` / 引理 `preHilbertPoly_eq_choose_sub_add`

English:
lemma preHilbertPoly_eq_choose_sub_add
  given: [CharZero F] (d : Nat) {k n : Nat} (hkn : k <= n)
  proof: by
  have : (d ! : F) != 0 := by norm_cast; positivity
  calc
  _ = (↑d !)⁻¹ * eval (↑(n - k + 1)) (ascPochhammer F d) := by simp [cast_sub hkn, preHilbertPoly]
  _ = (n - k + d).choose d := by
    rw [ascPochhammer_nat_eq_natCast_ascFactorial];
    simp [field, ascFactorial_eq_factorial_mul_choose]

中文:
引理 preHilbertPoly_eq_choose_sub_add
  条件: [CharZero F] (d : 自然数) {k n : 自然数} (hkn : k <= n)
  证明: by
  have : (d ! : F) != 0 := by norm_cast; positivity
  calc
  _ = (↑d !)⁻¹ * eval (↑(n - k + 1)) (ascPochhammer F d) := by simp [cast_sub hkn, preHilbertPoly]
  _ = (n - k + d).choose d := by
    rw [ascPochhammer_nat_eq_natCast_ascFactorial];
    simp [field, ascFactorial_eq_factorial_mul_choose]

Depends on / 依赖: ascFactorial_eq_factorial_mul_choose, ascPochhammer, ascPochhammer_nat_eq_natCast_ascFactorial, cast_sub, preHilbertPoly
-/
lemma preHilbertPoly_eq_choose_sub_add [CharZero F] (d : Nat) {k n : Nat} (hkn : k <= n) :
    (preHilbertPoly F d k).eval (n : F) = (n - k + d).choose d := by
  have : (d ! : F) != 0 := by norm_cast; positivity
  calc
  _ = (↑d !)⁻¹ * eval (↑(n - k + 1)) (ascPochhammer F d) := by simp [cast_sub hkn, preHilbertPoly]
  _ = (n - k + d).choose d := by
    rw [ascPochhammer_nat_eq_natCast_ascFactorial];
    simp [field, ascFactorial_eq_factorial_mul_choose]

variable {F}

/--
Definition of `hilbertPoly` / `hilbertPoly` 的定义

English:
definition hilbertPoly
  signature: (p : F[X])

中文:
定义 hilbertPoly
  签名: (p : F[X])
-/
noncomputable def hilbertPoly (p : F[X]) : (d : Nat) -> F[X]
  | 0 => 0
  | d + 1 => ∑ i in p.support, (p.coeff i) • preHilbertPoly F d i

/--
lemma `hilbertPoly_zero_left` / 引理 `hilbertPoly_zero_left`

English:
lemma hilbertPoly_zero_left
  given: (d : Nat)
  statement: hilbertPoly (0 : F[X]) d = 0
  proof: by
  delta hilbertPoly; induction d with
  | zero => simp only
  | succ d _ => simp only [coeff_zero, zero_smul, Finset.sum_const_zero]

中文:
引理 hilbertPoly_zero_left
  条件: (d : 自然数)
  结论: hilbertPoly (0 : F[X]) d = 0
  证明: by
  delta hilbertPoly; induction d with
  | zero => simp only
  | succ d _ => simp only [coeff_zero, zero_smul, Finset.sum_const_zero]

Depends on / 依赖: Finset, Finset.sum_const_zero, coeff_zero, hilbertPoly, sum_const_zero, zero_smul
-/
lemma hilbertPoly_zero_left (d : Nat) : hilbertPoly (0 : F[X]) d = 0 := by
  delta hilbertPoly; induction d with
  | zero => simp only
  | succ d _ => simp only [coeff_zero, zero_smul, Finset.sum_const_zero]

/--
lemma `hilbertPoly_zero_right` / 引理 `hilbertPoly_zero_right`

English:
lemma hilbertPoly_zero_right
  given: (p : F[X])
  statement: hilbertPoly p 0 = 0
  proof: rfl

中文:
引理 hilbertPoly_zero_right
  条件: (p : F[X])
  结论: hilbertPoly p 0 = 0
  证明: rfl
-/
lemma hilbertPoly_zero_right (p : F[X]) : hilbertPoly p 0 = 0 := rfl

/--
lemma `hilbertPoly_succ` / 引理 `hilbertPoly_succ`

English:
lemma hilbertPoly_succ
  given: (p : F[X]) (d : Nat)
  proof: rfl

中文:
引理 hilbertPoly_succ
  条件: (p : F[X]) (d : 自然数)
  证明: rfl
-/
lemma hilbertPoly_succ (p : F[X]) (d : Nat) :
    hilbertPoly p (d + 1) = ∑ i in p.support, (p.coeff i) • preHilbertPoly F d i := rfl

/--
lemma `hilbertPoly_X_pow_succ` / 引理 `hilbertPoly_X_pow_succ`

English:
lemma hilbertPoly_X_pow_succ
  given: (d k : Nat)
  proof: by
  delta hilbertPoly; simp

中文:
引理 hilbertPoly_X_pow_succ
  条件: (d k : 自然数)
  证明: by
  delta hilbertPoly; simp

Depends on / 依赖: hilbertPoly
-/
lemma hilbertPoly_X_pow_succ (d k : Nat) :
    hilbertPoly ((X : F[X]) ^ k) (d + 1) = preHilbertPoly F d k := by
  delta hilbertPoly; simp

/--
lemma `hilbertPoly_add_left` / 引理 `hilbertPoly_add_left`

English:
lemma hilbertPoly_add_left
  given: (p q : F[X]) (d : Nat)
  proof: by
  delta hilbertPoly
  induction d with
  | zero => simp only [add_zero]
  | succ d _ =>
      simp only
      rw [← sum_def _ fun _ r => r • _]
      exact sum_add_index _ _ _ (fun _ => zero_smul ..) (fun _ _ _ => add_smul ..)

中文:
引理 hilbertPoly_add_left
  条件: (p q : F[X]) (d : 自然数)
  证明: by
  delta hilbertPoly
  induction d with
  | zero => simp only [add_zero]
  | succ d _ =>
      simp only
      rw [← sum_def _ fun _ r => r • _]
      exact sum_add_index _ _ _ (fun _ => zero_smul ..) (fun _ _ _ => add_smul ..)

Depends on / 依赖: add_smul, add_zero, hilbertPoly, sum_add_index, sum_def, zero_smul
-/
lemma hilbertPoly_add_left (p q : F[X]) (d : Nat) :
    hilbertPoly (p + q) d = hilbertPoly p d + hilbertPoly q d := by
  delta hilbertPoly
  induction d with
  | zero => simp only [add_zero]
  | succ d _ =>
      simp only
      rw [← sum_def _ fun _ r => r • _]
      exact sum_add_index _ _ _ (fun _ => zero_smul ..) (fun _ _ _ => add_smul ..)

/--
lemma `hilbertPoly_smul` / 引理 `hilbertPoly_smul`

English:
lemma hilbertPoly_smul
  given: (a : F) (p : F[X]) (d : Nat)
  proof: by
  delta hilbertPoly
  induction d with
  | zero => simp only [smul_zero]
  | succ d _ =>
      simp only
      rw [← sum_def _ fun _ r => r • _]; rw [← sum_def _ fun _ r => r • _]; rw [Polynomial.smul_sum]; rw [sum_smul_index' _ _ _ fun i => zero_smul F (preHilbertPoly F d i)]
      simp only [sm

中文:
引理 hilbertPoly_smul
  条件: (a : F) (p : F[X]) (d : 自然数)
  证明: by
  delta hilbertPoly
  induction d with
  | zero => simp only [smul_zero]
  | succ d _ =>
      simp only
      rw [← sum_def _ fun _ r => r • _]; rw [← sum_def _ fun _ r => r • _]; rw [Polynomial.smul_sum]; rw [sum_smul_index' _ _ _ fun i => zero_smul F (preHilbertPoly F d i)]
      simp only [sm

Depends on / 依赖: Polynomial, Polynomial.smul_sum, hilbertPoly, preHilbertPoly, smul_assoc, smul_sum, smul_zero, sum_def, sum_smul_index, zero_smul
-/
lemma hilbertPoly_smul (a : F) (p : F[X]) (d : Nat) :
    hilbertPoly (a • p) d = a • hilbertPoly p d := by
  delta hilbertPoly
  induction d with
  | zero => simp only [smul_zero]
  | succ d _ =>
      simp only
      rw [← sum_def _ fun _ r => r • _]; rw [← sum_def _ fun _ r => r • _]; rw [Polynomial.smul_sum]; rw [sum_smul_index' _ _ _ fun i => zero_smul F (preHilbertPoly F d i)]
      simp only [smul_assoc]

variable (F) in
/--
Definition of `hilbertPoly_linearMap` / `hilbertPoly_linearMap` 的定义

English:
definition hilbertPoly_linearMap
  signature: (d : Nat)
  body: hilbertPoly p d
  map_add' p q := hilbertPoly_add_left p q d
  map_smul' r p := hilbertPoly_smul r p d

中文:
定义 hilbertPoly_linearMap
  签名: (d : 自然数)
  定义体: hilbertPoly p d
  map_add' p q := hilbertPoly_add_left p q d
  map_smul' r p := hilbertPoly_smul r p d

Depends on / 依赖: hilbertPoly
-/
noncomputable def hilbertPoly_linearMap (d : Nat) : F[X] ->ₗ[F] F[X] where
  toFun p := hilbertPoly p d
  map_add' p q := hilbertPoly_add_left p q d
  map_smul' r p := hilbertPoly_smul r p d

variable [CharZero F]

/--
theorem `coeff_mul_invOneSubPow_eq_hilbertPoly_eval` / 定理 `coeff_mul_invOneSubPow_eq_hilbertPoly_eval`

English:
theorem coeff_mul_invOneSubPow_eq_hilbertPoly_eval
  proof: by
  delta hilbertPoly; induction d with
  | zero => simp only [invOneSubPow_zero, Units.val_one, mul_one, coeff_coe, eval_zero]
            exact coeff_eq_zero_of_natDegree_lt hn
  | succ d hd =>
      simp only [eval_finsetSum, eval_smul, smul_eq_mul]
      rw [← Finset.sum_coe_sort]
      have h_

中文:
定理 coeff_mul_invOneSubPow_eq_hilbertPoly_eval
  证明: by
  delta hilbertPoly; induction d with
  | zero => simp only [invOneSubPow_zero, Units.val_one, mul_one, coeff_coe, eval_zero]
            exact coeff_eq_zero_of_natDegree_lt hn
  | succ d hd =>
      simp only [eval_finsetSum, eval_smul, smul_eq_mul]
      rw [← Finset.sum_coe_sort]
      have h_

Depends on / 依赖: Finset, Finset.sum_coe_sort, Units.val_one, coeff_coe, coeff_eq_zero_of_natDegree_lt, eval_finsetSum, eval_smul, eval_zero, h_le, hilbertPoly, hn.le, invOneSubPow_zero, le_natDegree_of_ne_zero, le_trans, mem_support_iff, mul_one, p.support, preHilbertPoly, preHilbertPoly_eq_choose_sub_add, smul_eq_mul
-/
theorem coeff_mul_invOneSubPow_eq_hilbertPoly_eval
    {p : F[X]} (d : Nat) {n : Nat} (hn : p.natDegree < n) :
    (p * invOneSubPow F d : F⟦X⟧).coeff n = (hilbertPoly p d).eval (n : F) := by
  delta hilbertPoly; induction d with
  | zero => simp only [invOneSubPow_zero, Units.val_one, mul_one, coeff_coe, eval_zero]
            exact coeff_eq_zero_of_natDegree_lt hn
  | succ d hd =>
      simp only [eval_finsetSum, eval_smul, smul_eq_mul]
      rw [← Finset.sum_coe_sort]
      have h_le (i : p.support) : (i : Nat) <= n :=
        le_trans (le_natDegree_of_ne_zero <| mem_support_iff.1 i.2) hn.le
      have h (i : p.support) : eval ↑n (preHilbertPoly F d ↑i) = (n + d - ↑i).choose d := by
        rw [preHilbertPoly_eq_choose_sub_add _ _ (h_le i)]; rw [Nat.sub_add_comm (h_le i)]
      simp_rw [h]
      rw [Finset.sum_coe_sort _ (fun x => (p.coeff ↑x) * (_ + d - ↑x).choose _)]; rw [PowerSeries.coeff_mul]; rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rw [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (zero_lt_succ d)]
      simp only [coeff_coe, coeff_mk]
      symm
      refine Finset.sum_subset_zero_on_sdiff (fun s hs => ?_) (fun x hx => ?_) (fun x hx => ?_)
      · rw [Finset.mem_range_succ_iff]
        exact h_le ⟨s, hs⟩
      · simp only [Finset.mem_sdiff, mem_support_iff, not_not] at hx
        rw [hx.2]; rw [zero_mul]
      · rw [add_comm, Nat.add_sub_assoc (h_le ⟨x, hx⟩), succ_eq_add_one, add_tsub_cancel_right]

/--
theorem `existsUnique_hilbertPoly` / 定理 `existsUnique_hilbertPoly`

English:
theorem existsUnique_hilbertPoly
  given: (p : F[X]) (d : Nat)
  proof: by
  use hilbertPoly p d; constructor
  · use p.natDegree
    exact fun n => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d
  · rintro h ⟨N, hhN⟩
    apply eq_of_infinite_eval_eq h (hilbertPoly p d)
    apply ((Set.Ioi_infinite (max N p.natDegree)).image cast_injective.injOn).mono
    rintro x ⟨n, hn,

中文:
定理 existsUnique_hilbertPoly
  条件: (p : F[X]) (d : 自然数)
  证明: by
  use hilbertPoly p d; constructor
  · use p.natDegree
    exact fun n => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d
  · rintro h ⟨N, hhN⟩
    apply eq_of_infinite_eval_eq h (hilbertPoly p d)
    apply ((Set.Ioi_infinite (max N p.natDegree)).image cast_injective.injOn).mono
    rintro x ⟨n, hn,

Depends on / 依赖: Ioi_infinite, Set.Ioi_infinite, Set.mem_Ioi, Set.mem_ofPred_eq, cast_injective, cast_injective.injOn, coeff_mul_invOneSubPow_eq_hilbertPoly_eval, eq_of_infinite_eval_eq, hilbertPoly, mem_Ioi, mem_ofPred_eq, natDegree, p.natDegree, sup_lt_iff
-/
theorem existsUnique_hilbertPoly (p : F[X]) (d : Nat) :
    exists! h : F[X], exists N : Nat, forall n > N,
      (p * invOneSubPow F d : F⟦X⟧).coeff n = h.eval (n : F) := by
  use hilbertPoly p d; constructor
  · use p.natDegree
    exact fun n => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d
  · rintro h ⟨N, hhN⟩
    apply eq_of_infinite_eval_eq h (hilbertPoly p d)
    apply ((Set.Ioi_infinite (max N p.natDegree)).image cast_injective.injOn).mono
    rintro x ⟨n, hn, rfl⟩
    simp only [Set.mem_Ioi, sup_lt_iff, Set.mem_ofPred_eq] at hn ⊢
    rw [← coeff_mul_invOneSubPow_eq_hilbertPoly_eval d hn.2]; rw [hhN n hn.1]

/--
theorem `eq_hilbertPoly_of_forall_coeff_eq_eval` / 定理 `eq_hilbertPoly_of_forall_coeff_eq_eval`

English:
theorem eq_hilbertPoly_of_forall_coeff_eq_eval
  proof: ExistsUnique.unique (existsUnique_hilbertPoly p d) ⟨N, hhN⟩
    ⟨p.natDegree, fun _ x => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d x⟩

中文:
定理 eq_hilbertPoly_of_forall_coeff_eq_eval
  证明: ExistsUnique.unique (existsUnique_hilbertPoly p d) ⟨N, hhN⟩
    ⟨p.natDegree, fun _ x => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d x⟩

Depends on / 依赖: h.eval, invOneSubPow
-/
theorem eq_hilbertPoly_of_forall_coeff_eq_eval
    {p h : F[X]} {d : Nat} (N : Nat) (hhN : forall n > N,
    PowerSeries.coeff (R := F) n (p * invOneSubPow F d) = h.eval (n : F)) :
    h = hilbertPoly p d :=
  ExistsUnique.unique (existsUnique_hilbertPoly p d) ⟨N, hhN⟩
    ⟨p.natDegree, fun _ x => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d x⟩

/--
lemma `hilbertPoly_mul_one_sub_succ` / 引理 `hilbertPoly_mul_one_sub_succ`

English:
lemma hilbertPoly_mul_one_sub_succ
  given: (p : F[X]) (d : Nat)
  proof: by
  apply eq_hilbertPoly_of_forall_coeff_eq_eval (p * (1 - X)).natDegree
  intro n hn
  have heq : 1 - PowerSeries.X = ((1 - X : F[X]) : F⟦X⟧) := by simp only [coe_sub, coe_one, coe_X]
  rw [← one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val F d 1]; rw [pow_one]; rw [← mul_assoc]; rw [heq];

中文:
引理 hilbertPoly_mul_one_sub_succ
  条件: (p : F[X]) (d : 自然数)
  证明: by
  apply eq_hilbertPoly_of_forall_coeff_eq_eval (p * (1 - X)).natDegree
  intro n hn
  have heq : 1 - PowerSeries.X = ((1 - X : F[X]) : F⟦X⟧) := by simp only [coe_sub, coe_one, coe_X]
  rw [← one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val F d 1]; rw [pow_one]; rw [← mul_assoc]; rw [heq];

Depends on / 依赖: PowerSeries, PowerSeries.X, coe_X, coe_mul, coe_one, coe_sub, coeff_mul_invOneSubPow_eq_hilbertPoly_eval, eq_hilbertPoly_of_forall_coeff_eq_eval, mul_assoc, natDegree, one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val, pow_one
-/
lemma hilbertPoly_mul_one_sub_succ (p : F[X]) (d : Nat) :
    hilbertPoly (p * (1 - X)) (d + 1) = hilbertPoly p d := by
  apply eq_hilbertPoly_of_forall_coeff_eq_eval (p * (1 - X)).natDegree
  intro n hn
  have heq : 1 - PowerSeries.X = ((1 - X : F[X]) : F⟦X⟧) := by simp only [coe_sub, coe_one, coe_X]
  rw [← one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val F d 1]; rw [pow_one]; rw [← mul_assoc]; rw [heq]; rw [← coe_mul]; rw [coeff_mul_invOneSubPow_eq_hilbertPoly_eval (d + 1) hn]

/--
lemma `hilbertPoly_mul_one_sub_pow_add` / 引理 `hilbertPoly_mul_one_sub_pow_add`

English:
lemma hilbertPoly_mul_one_sub_pow_add
  given: (p : F[X]) (d e : Nat)
  proof: by
  induction e with
  | zero => simp
  | succ e he => rw [pow_add, pow_one, ← mul_assoc, ← add_assoc, hilbertPoly_mul_one_sub_succ, he]

中文:
引理 hilbertPoly_mul_one_sub_pow_add
  条件: (p : F[X]) (d e : 自然数)
  证明: by
  induction e with
  | zero => simp
  | succ e he => rw [pow_add, pow_one, ← mul_assoc, ← add_assoc, hilbertPoly_mul_one_sub_succ, he]

Depends on / 依赖: add_assoc, hilbertPoly_mul_one_sub_succ, mul_assoc, pow_add, pow_one
-/
lemma hilbertPoly_mul_one_sub_pow_add (p : F[X]) (d e : Nat) :
    hilbertPoly (p * (1 - X) ^ e) (d + e) = hilbertPoly p d := by
  induction e with
  | zero => simp
  | succ e he => rw [pow_add, pow_one, ← mul_assoc, ← add_assoc, hilbertPoly_mul_one_sub_succ, he]

/--
lemma `hilbertPoly_eq_zero_of_le_rootMultiplicity_one` / 引理 `hilbertPoly_eq_zero_of_le_rootMultiplicity_one`

English:
lemma hilbertPoly_eq_zero_of_le_rootMultiplicity_one
  proof: by
  by_cases hp : p = 0
  · rw [hp, hilbertPoly_zero_left]
  · rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1 with ⟨q, hq1, hq2⟩
    have heq : p = q * (-1) ^ p.rootMultiplicity 1 * (1 - X) ^ p.rootMultiplicity 1 := by
      simp only [mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]


中文:
引理 hilbertPoly_eq_zero_of_le_rootMultiplicity_one
  证明: by
  by_cases hp : p = 0
  · rw [hp, hilbertPoly_zero_left]
  · rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1 with ⟨q, hq1, hq2⟩
    have heq : p = q * (-1) ^ p.rootMultiplicity 1 * (1 - X) ^ p.rootMultiplicity 1 := by
      simp only [mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]


Depends on / 依赖: Nat.sub_add_cancel, exists_eq_pow_rootMultiplicity_mul_and_not_dvd, hilbertPoly, hilbertPoly_mul_one_sub_pow_add, hilbertPoly_zero_left, hq1.trans, mul_assoc, mul_comm, mul_pow, neg_mul, neg_sub, one_mul, p.rootMultiplicity, pow_add, rootMultiplicity, sub_add_cancel, zero_add
-/
lemma hilbertPoly_eq_zero_of_le_rootMultiplicity_one
    {p : F[X]} {d : Nat} (hdp : d <= p.rootMultiplicity 1) :
    hilbertPoly p d = 0 := by
  by_cases hp : p = 0
  · rw [hp, hilbertPoly_zero_left]
  · rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1 with ⟨q, hq1, hq2⟩
    have heq : p = q * (-1) ^ p.rootMultiplicity 1 * (1 - X) ^ p.rootMultiplicity 1 := by
      simp only [mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]
      exact hq1.trans (mul_comm _ _)
    rw [heq]; rw [← zero_add d]; rw [← Nat.sub_add_cancel hdp]; rw [pow_add (1 - X)]; rw [← mul_assoc]; rw [hilbertPoly_mul_one_sub_pow_add]; rw [hilbertPoly]

/--
theorem `natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt` / 定理 `natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt`

English:
theorem natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt
  proof: by
  rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1 with ⟨q, hq1, hq2⟩
  have heq : p = q * (-1) ^ p.rootMultiplicity 1 * (1 - X) ^ p.rootMultiplicity 1 := by
    simp only [mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]
    exact hq1.trans (mul_comm _ _)
  nth_rw 1 [heq, ← Nat.sub_a

中文:
定理 natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt
  证明: by
  rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1 with ⟨q, hq1, hq2⟩
  have heq : p = q * (-1) ^ p.rootMultiplicity 1 * (1 - X) ^ p.rootMultiplicity 1 := by
    simp only [mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]
    exact hq1.trans (mul_comm _ _)
  nth_rw 1 [heq, ← Nat.sub_a

Depends on / 依赖: Nat.le_sub_of_add_le, Nat.sub_add_cancel, add_one_le_of_lt, exists_eq_pow_rootMultiplicity_mul_and_not_dvd, hilbertPoly, hilbertPoly_mul_one_sub_pow_add, hq1.trans, le_of_lt, le_sub_of_add_le, mul_assoc, mul_comm, mul_pow, natDegree_eq_of_le_of_coeff_ne_zero, natDegree_sum_le_, neg_mul, neg_sub, nth_rw, one_mul, p.rootMultiplicity, rootMultiplicity
-/
theorem natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt
    {p : F[X]} {d : Nat} (hp : p != 0) (hpd : p.rootMultiplicity 1 < d) :
    (hilbertPoly p d).natDegree = d - p.rootMultiplicity 1 - 1 := by
  rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1 with ⟨q, hq1, hq2⟩
  have heq : p = q * (-1) ^ p.rootMultiplicity 1 * (1 - X) ^ p.rootMultiplicity 1 := by
    simp only [mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]
    exact hq1.trans (mul_comm _ _)
  nth_rw 1 [heq, ← Nat.sub_add_cancel (le_of_lt hpd), hilbertPoly_mul_one_sub_pow_add,
    ← Nat.sub_add_cancel (Nat.le_sub_of_add_le' <| add_one_le_of_lt hpd)]
  delta hilbertPoly
  apply natDegree_eq_of_le_of_coeff_ne_zero
· apply natDegree_sum_le_of_forall_le _ _ fun _ _ => ?_
    apply le_trans (natDegree_smul_le _ _)
    rw [natDegree_preHilbertPoly]
  · have : (fun (x : Nat) (a : F) => a) = fun x a => a * 1 ^ x := by simp only [one_pow, mul_one]
    simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_preHilbertPoly_self,
      ← Finset.sum_mul, ← sum_def _ (fun _ a => a), this, ← eval_eq_sum, eval_mul, eval_pow,
      eval_neg, eval_one, _root_.mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq,
      false_and, or_false, inv_eq_zero, cast_eq_zero, not_or]
    exact ⟨(not_iff_not.2 dvd_iff_isRoot).1 hq2, factorial_ne_zero _⟩

/--
theorem `natDegree_hilbertPoly_of_ne_zero` / 定理 `natDegree_hilbertPoly_of_ne_zero`

English:
theorem natDegree_hilbertPoly_of_ne_zero
  proof: by
  have hp : p != 0 := by
    intro h
    rw [h] at hh
    exact hh (hilbertPoly_zero_left d)
  have hpd : p.rootMultiplicity 1 < d := by
    by_contra h
    exact hh (hilbertPoly_eq_zero_of_le_rootMultiplicity_one <| not_lt.1 h)
  exact natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt hp h

中文:
定理 natDegree_hilbertPoly_of_ne_zero
  证明: by
  have hp : p != 0 := by
    intro h
    rw [h] at hh
    exact hh (hilbertPoly_zero_left d)
  have hpd : p.rootMultiplicity 1 < d := by
    by_contra h
    exact hh (hilbertPoly_eq_zero_of_le_rootMultiplicity_one <| not_lt.1 h)
  exact natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt hp h

Depends on / 依赖: hilbertPoly_eq_zero_of_le_rootMultiplicity_one, hilbertPoly_zero_left, natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt, not_lt, p.rootMultiplicity, rootMultiplicity
-/
theorem natDegree_hilbertPoly_of_ne_zero
    {p : F[X]} {d : Nat} (hh : hilbertPoly p d != 0) :
    (hilbertPoly p d).natDegree = d - p.rootMultiplicity 1 - 1 := by
  have hp : p != 0 := by
    intro h
    rw [h] at hh
    exact hh (hilbertPoly_zero_left d)
  have hpd : p.rootMultiplicity 1 < d := by
    by_contra h
    exact hh (hilbertPoly_eq_zero_of_le_rootMultiplicity_one <| not_lt.1 h)
  exact natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt hp hpd

end Polynomial
