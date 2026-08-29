/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Tactic.ByContra
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Analysis.Complex.Arg

/-!
# Evaluating cyclotomic polynomials

This file states some results about evaluating cyclotomic polynomials in various different ways.

## Main definitions
* `Polynomial.eval(₂)_one_cyclotomic_prime(_pow)`: `eval 1 (cyclotomic p^k R) = p`.
* `Polynomial.eval_one_cyclotomic_not_prime_pow`: Otherwise, `eval 1 (cyclotomic n R) = 1`.
* `Polynomial.cyclotomic_pos` : `∀ x, 0 < eval x (cyclotomic n R)` if `2 < n`.
-/

public section


namespace Polynomial

open Finset Nat

@[simp]
/--
theorem `eval_one_cyclotomic_prime` / 定理 `eval_one_cyclotomic_prime`

English:
theorem eval_one_cyclotomic_prime
  given: {R : Type*} [CommRing R] {p : Nat} [hn : Fact p.Prime]
  proof: by
  simp only [cyclotomic_prime, eval_X, one_pow, Finset.sum_const, eval_pow, eval_finsetSum,
    Finset.card_range, smul_one_eq_cast]

中文:
定理 eval_one_cyclotomic_prime
  条件: {R : 类型} [交换环 R] {p : 自然数} [hn : Fact p.素]
  证明: by
  simp only [cyclotomic_prime, eval_X, one_pow, Finset.sum_const, eval_pow, eval_finsetSum,
    Finset.card_range, smul_one_eq_cast]

Depends on / 依赖: Finset, Finset.card_range, Finset.sum_const, card_range, cyclotomic_prime, eval_X, eval_finsetSum, eval_pow, one_pow, smul_one_eq_cast, sum_const
-/
theorem eval_one_cyclotomic_prime {R : Type*} [CommRing R] {p : Nat} [hn : Fact p.Prime] :
    eval 1 (cyclotomic p R) = p := by
  simp only [cyclotomic_prime, eval_X, one_pow, Finset.sum_const, eval_pow, eval_finsetSum,
    Finset.card_range, smul_one_eq_cast]

/--
theorem `eval₂_one_cyclotomic_prime` / 定理 `eval₂_one_cyclotomic_prime`

English:
theorem eval₂_one_cyclotomic_prime
  statement: {R S : Type*} [CommRing R] [Semiring S] (f : R ->+* S) {p : Nat}
  proof: by simp

@[simp]

中文:
定理 eval₂_one_cyclotomic_prime
  结论: {R S : 类型} [交换环 R] [半环 S] (f : R ->+* S) {p : 自然数}
  证明: by simp

@[simp]
-/
theorem eval₂_one_cyclotomic_prime {R S : Type*} [CommRing R] [Semiring S] (f : R ->+* S) {p : Nat}
    [Fact p.Prime] : eval₂ f 1 (cyclotomic p R) = p := by simp

@[simp]
/--
theorem `eval_one_cyclotomic_prime_pow` / 定理 `eval_one_cyclotomic_prime_pow`

English:
theorem eval_one_cyclotomic_prime_pow
  statement: {R : Type*} [CommRing R] {p : Nat} (k : Nat)
  proof: by
  simp only [cyclotomic_prime_pow_eq_geom_sum hn.out, eval_X, one_pow, Finset.sum_const, eval_pow,
    eval_finsetSum, Finset.card_range, smul_one_eq_cast]

中文:
定理 eval_one_cyclotomic_prime_pow
  结论: {R : 类型} [交换环 R] {p : 自然数} (k : 自然数)
  证明: by
  simp only [cyclotomic_prime_pow_eq_geom_sum hn.out, eval_X, one_pow, Finset.sum_const, eval_pow,
    eval_finsetSum, Finset.card_range, smul_one_eq_cast]

Depends on / 依赖: Finset, Finset.card_range, Finset.sum_const, card_range, cyclotomic_prime_pow_eq_geom_sum, eval_X, eval_finsetSum, eval_pow, hn.out, one_pow, smul_one_eq_cast, sum_const
-/
theorem eval_one_cyclotomic_prime_pow {R : Type*} [CommRing R] {p : Nat} (k : Nat)
    [hn : Fact p.Prime] : eval 1 (cyclotomic (p ^ (k + 1)) R) = p := by
  simp only [cyclotomic_prime_pow_eq_geom_sum hn.out, eval_X, one_pow, Finset.sum_const, eval_pow,
    eval_finsetSum, Finset.card_range, smul_one_eq_cast]

/--
theorem `eval₂_one_cyclotomic_prime_pow` / 定理 `eval₂_one_cyclotomic_prime_pow`

English:
theorem eval₂_one_cyclotomic_prime_pow
  statement: {R S : Type*} [CommRing R] [Semiring S] (f : R ->+* S)
  proof: by simp

中文:
定理 eval₂_one_cyclotomic_prime_pow
  结论: {R S : 类型} [交换环 R] [半环 S] (f : R ->+* S)
  证明: by simp
-/
theorem eval₂_one_cyclotomic_prime_pow {R S : Type*} [CommRing R] [Semiring S] (f : R ->+* S)
    {p : Nat} (k : Nat) [Fact p.Prime] : eval₂ f 1 (cyclotomic (p ^ (k + 1)) R) = p := by simp

/--
theorem `cyclotomic_neg_one_pos` / 定理 `cyclotomic_neg_one_pos`

English:
theorem cyclotomic_neg_one_pos
  statement: {n : Nat} (hn : 2 < n) {R}
  proof: by
  have := NeZero.of_gt hn
  rw [← map_cyclotomic_int]; rw [← Int.cast_one]; rw [← Int.cast_neg]; rw [eval_intCast_map]; rw [Int.coe_castRingHom]; rw [Int.cast_pos]
  suffices 0 < eval (↑(-1 : Int)) (cyclotomic n Real) by
    rw [← map_cyclotomic_int n Real]; rw [eval_intCast_map]; rw [Int.coe_cas

中文:
定理 cyclotomic_neg_one_pos
  结论: {n : 自然数} (hn : 2 < n) {R}
  证明: by
  have := NeZero.of_gt hn
  rw [← map_cyclotomic_int]; rw [← Int.cast_one]; rw [← Int.cast_neg]; rw [eval_intCast_map]; rw [Int.coe_castRingHom]; rw [Int.cast_pos]
  suffices 0 < eval (↑(-1 : Int)) (cyclotomic n Real) by
    rw [← map_cyclotomic_int n Real]; rw [eval_intCast_map]; rw [Int.coe_cas
-/
private theorem cyclotomic_neg_one_pos {n : Nat} (hn : 2 < n) {R}
    [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] :
    0 < eval (-1 : R) (cyclotomic n R) := by
  have := NeZero.of_gt hn
  rw [← map_cyclotomic_int]; rw [← Int.cast_one]; rw [← Int.cast_neg]; rw [eval_intCast_map]; rw [Int.coe_castRingHom]; rw [Int.cast_pos]
  suffices 0 < eval (↑(-1 : Int)) (cyclotomic n Real) by
    rw [← map_cyclotomic_int n Real]; rw [eval_intCast_map]; rw [Int.coe_castRingHom] at this
    simpa only [Int.cast_pos] using this
  simp only [Int.cast_one, Int.cast_neg]
  have h0 := cyclotomic_coeff_zero Real hn.le
  rw [coeff_zero_eq_eval_zero] at h0
  by_contra! hx
  have := intermediate_value_univ (-1) 0 (cyclotomic n Real).continuous
  obtain ⟨y, hy : IsRoot _ y⟩ := this (show (0 : Real) in Set.Icc _ _ by simpa [h0] using hx)
  rw [@isRoot_cyclotomic_iff] at hy
  rw [hy.eq_orderOf] at hn
  exact hn.not_ge LinearOrderedRing.orderOf_le_two

/--
theorem `cyclotomic_pos` / 定理 `cyclotomic_pos`

English:
theorem cyclotomic_pos
  statement: {n : Nat} (hn : 2 < n) {R}
  proof: by
  induction n using Nat.strong_induction_on with | _ n ih
  have hn' : 0 < n := pos_of_gt hn
  have hn'' : 1 < n := one_lt_two.trans hn
  have := prod_cyclotomic_eq_geom_sum hn' R
  apply_fun eval x at this
  rw [← cons_self_properDivisors hn'.ne']; rw [Finset.erase_cons_of_ne _ hn''.ne']; rw [Fi

中文:
定理 cyclotomic_pos
  结论: {n : 自然数} (hn : 2 < n) {R}
  证明: by
  induction n using Nat.strong_induction_on with | _ n ih
  have hn' : 0 < n := pos_of_gt hn
  have hn'' : 1 < n := one_lt_two.trans hn
  have := prod_cyclotomic_eq_geom_sum hn' R
  apply_fun eval x at this
  rw [← cons_self_properDivisors hn'.ne']; rw [Finset.erase_cons_of_ne _ hn''.ne']; rw [Fi

Depends on / 依赖: Finset, Finset.erase_cons_of_ne, Finset.prod_cons, Finset.prod_nonneg, Finset.range, Nat.strong_induction_on, apply_fun, cons_self_properDivisors, erase_cons_of_ne, eval_geom_sum, eval_mul, eval_prod, lt_trichotomy, one_lt_two, one_lt_two.trans, pos_of_gt, pos_of_mul_pos_left, prod_cons, prod_cyclotomic_eq_geom_sum, prod_nonneg
-/
theorem cyclotomic_pos {n : Nat} (hn : 2 < n) {R}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) :
    0 < eval x (cyclotomic n R) := by
  induction n using Nat.strong_induction_on with | _ n ih
  have hn' : 0 < n := pos_of_gt hn
  have hn'' : 1 < n := one_lt_two.trans hn
  have := prod_cyclotomic_eq_geom_sum hn' R
  apply_fun eval x at this
  rw [← cons_self_properDivisors hn'.ne']; rw [Finset.erase_cons_of_ne _ hn''.ne']; rw [Finset.prod_cons]; rw [eval_mul]; rw [eval_geom_sum] at this
  rcases lt_trichotomy 0 (∑ i in Finset.range n, x ^ i) with (h | h | h)
  · apply pos_of_mul_pos_left
    · rwa [this]
    rw [eval_prod]
    refine Finset.prod_nonneg fun i hi => ?_
    simp only [Finset.mem_erase, mem_properDivisors] at hi
    rw [geom_sum_pos_iff hn'.ne'] at h
    rcases h with hk | hx
    · refine (ih _ hi.2.2 (Nat.two_lt_of_ne ?_ hi.1 ?_)).le <;> rintro rfl
      · exact hn'.ne' (zero_dvd_iff.mp hi.2.1)
      · exact not_odd_iff_even.2 (even_iff_two_dvd.mpr hi.2.1) hk
    · rcases eq_or_ne i 2 with (rfl | hk)
      · simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using hx.le
      refine (ih _ hi.2.2 (Nat.two_lt_of_ne ?_ hi.1 hk)).le
      rintro rfl
exact hn'.ne' zero_dvd_iff.mp hi.2.1
  · rw [eq_comm, geom_sum_eq_zero_iff_neg_one hn'.ne'] at h
    exact h.1.symm ▸ cyclotomic_neg_one_pos hn
  · apply pos_of_mul_neg_left
    · rwa [this]
    rw [geom_sum_neg_iff hn'.ne'] at h
    have h2 : 2 in n.properDivisors.erase 1 := by
      rw [Finset.mem_erase]; rw [mem_properDivisors]
      exact ⟨by decide, even_iff_two_dvd.mp h.1, hn⟩
    rw [eval_prod]; rw [← Finset.prod_erase_mul _ _ h2]
    apply mul_nonpos_of_nonneg_of_nonpos
    · refine Finset.prod_nonneg fun i hi => le_of_lt ?_
      simp only [Finset.mem_erase, mem_properDivisors] at hi
      refine ih _ hi.2.2.2 (Nat.two_lt_of_ne ?_ hi.2.1 hi.1)
      rintro rfl
      rw [zero_dvd_iff] at hi
      exact hn'.ne' hi.2.2.1
    · simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using h.right.le

/--
theorem `cyclotomic_pos_and_nonneg` / 定理 `cyclotomic_pos_and_nonneg`

English:
theorem cyclotomic_pos_and_nonneg
  statement: (n : Nat) {R}
  proof: by
  rcases n with (_ | _ | _ | n)
  · simp only [cyclotomic_zero, eval_one, zero_lt_one, implies_true, zero_le_one, and_self]
  · simp
  · simp only [zero_add, reduceAdd, cyclotomic_two, eval_add, eval_X, eval_one]
    constructor <;> intro <;> linarith
  · constructor <;> intro <;> [skip; apply le

中文:
定理 cyclotomic_pos_and_nonneg
  结论: (n : 自然数) {R}
  证明: by
  rcases n with (_ | _ | _ | n)
  · simp only [cyclotomic_zero, eval_one, zero_lt_one, implies_true, zero_le_one, and_self]
  · simp
  · simp only [zero_add, reduceAdd, cyclotomic_two, eval_add, eval_X, eval_one]
    constructor <;> intro <;> linarith
  · constructor <;> intro <;> [skip; apply le

Depends on / 依赖: and_self, cyclotomic_pos, cyclotomic_two, cyclotomic_zero, eval_X, eval_add, eval_one, implies_true, le_of_lt, reduceAdd, zero_add, zero_le_one, zero_lt_one
-/
theorem cyclotomic_pos_and_nonneg (n : Nat) {R}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) :
    (1 < x -> 0 < eval x (cyclotomic n R)) ∧ (1 <= x -> 0 <= eval x (cyclotomic n R)) := by
  rcases n with (_ | _ | _ | n)
  · simp only [cyclotomic_zero, eval_one, zero_lt_one, implies_true, zero_le_one, and_self]
  · simp
  · simp only [zero_add, reduceAdd, cyclotomic_two, eval_add, eval_X, eval_one]
    constructor <;> intro <;> linarith
  · constructor <;> intro <;> [skip; apply le_of_lt] <;> apply cyclotomic_pos (by lia)

/--
theorem `cyclotomic_pos'` / 定理 `cyclotomic_pos'`

English:
theorem cyclotomic_pos'
  statement: (n : Nat) {R}
  proof: (cyclotomic_pos_and_nonneg n x).1 hx

中文:
定理 cyclotomic_pos'
  结论: (n : 自然数) {R}
  证明: (cyclotomic_pos_and_nonneg n x).1 hx

Depends on / 依赖: cyclotomic_pos_and_nonneg
-/
theorem cyclotomic_pos' (n : Nat) {R}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {x : R} (hx : 1 < x) :
    0 < eval x (cyclotomic n R) :=
  (cyclotomic_pos_and_nonneg n x).1 hx

/--
theorem `cyclotomic_nonneg` / 定理 `cyclotomic_nonneg`

English:
theorem cyclotomic_nonneg
  statement: (n : Nat) {R}
  proof: (cyclotomic_pos_and_nonneg n x).2 hx

中文:
定理 cyclotomic_nonneg
  结论: (n : 自然数) {R}
  证明: (cyclotomic_pos_and_nonneg n x).2 hx

Depends on / 依赖: cyclotomic_pos_and_nonneg
-/
theorem cyclotomic_nonneg (n : Nat) {R}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {x : R} (hx : 1 <= x) :
    0 <= eval x (cyclotomic n R) :=
  (cyclotomic_pos_and_nonneg n x).2 hx

/--
theorem `eval_one_cyclotomic_not_prime_pow` / 定理 `eval_one_cyclotomic_not_prime_pow`

English:
theorem eval_one_cyclotomic_not_prime_pow
  statement: {R : Type*} [Ring R] {n : Nat}
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn')
  · simp
  have hn : 1 < n := one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn'.ne', (h Nat.prime_two 0).symm⟩
  rsuffices h | h : eval 1 (cyclotomic n Int) = 1 ∨ eval 1 (cyclotomic n Int) = -1
  · have := eval_intCast_map (Int.castRingHom R) (cyclotomic n Int) 1
 

中文:
定理 eval_one_cyclotomic_not_prime_pow
  结论: {R : 类型} [环 R] {n : 自然数}
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn')
  · simp
  have hn : 1 < n := one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn'.ne', (h Nat.prime_two 0).symm⟩
  rsuffices h | h : eval 1 (cyclotomic n Int) = 1 ∨ eval 1 (cyclotomic n Int) = -1
  · have := eval_intCast_map (Int.castRingHom R) (cyclotomic n Int) 1
 

Depends on / 依赖: Int.castRingHom, Int.cast_one, Int.natAbs_eq_natAbs_iff, Int.natAbs_one, Nat.eq_one_iff_not_exist, Nat.prime_two, castRingHom, cast_one, cyclotomic, cyclotomic_nonneg, eq_intCast, eq_one_iff_not_exist, eq_zero_or_pos, eval_intCast_map, le_refl, map_cyclotomic, n.eq_zero_or_pos, natAbs_eq_natAbs_iff, natAbs_one, one_lt_iff_ne_zero_and_ne_one
-/
theorem eval_one_cyclotomic_not_prime_pow {R : Type*} [Ring R] {n : Nat}
    (h : forall {p : Nat}, p.Prime -> forall k : Nat, p ^ k != n) : eval 1 (cyclotomic n R) = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn')
  · simp
  have hn : 1 < n := one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn'.ne', (h Nat.prime_two 0).symm⟩
  rsuffices h | h : eval 1 (cyclotomic n Int) = 1 ∨ eval 1 (cyclotomic n Int) = -1
  · have := eval_intCast_map (Int.castRingHom R) (cyclotomic n Int) 1
    simpa only [map_cyclotomic, Int.cast_one, h, eq_intCast] using this
  · exfalso
    linarith [cyclotomic_nonneg n (le_refl (1 : Int))]
  rw [← Int.natAbs_eq_natAbs_iff]; rw [Int.natAbs_one]; rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpe
  have := Fact.mk hp
  have := prod_cyclotomic_eq_geom_sum hn' Int
  apply_fun eval 1 at this
  rw [eval_geom_sum]; rw [one_geom_sum]; rw [eval_prod]; rw [eq_comm]; rw [←
Finset.prod_sdiff @range_pow_padicValNat_subset_divisors' p _ _]; rw [Finset.prod_image] at this
  · simp_rw [eval_one_cyclotomic_prime_pow, Finset.prod_const, Finset.card_range, mul_comm] at this
    rw [← Finset.prod_sdiff (s₁ := {n})] at this
    swap
    · simp only [singleton_subset_iff, mem_sdiff, mem_erase, Ne, mem_divisors, dvd_refl,
        true_and, mem_image, mem_range, not_exists, not_and]
      exact ⟨⟨hn.ne', hn'.ne'⟩, fun t _ => h hp _⟩
    rw [← Int.natAbs_natCast p]; rw [Int.natAbs_dvd_natAbs] at hpe
    obtain ⟨t, ht⟩ := hpe
    rw [Finset.prod_singleton]; rw [ht]; rw [mul_left_comm]; rw [mul_comm]; rw [← mul_assoc]; rw [mul_assoc] at this
    have : (p : Int) ^ padicValNat p n * p ∣ n := ⟨_, this⟩
    simp only [← _root_.pow_succ, ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast,
      Int.natAbs_pow] at this
    exact pow_succ_padicValNat_not_dvd hn'.ne' this
  · rintro x - y - hxy
    apply Nat.succ_injective
    exact Nat.pow_right_injective hp.two_le hxy

/--
theorem `sub_one_pow_totient_lt_cyclotomic_eval` / 定理 `sub_one_pow_totient_lt_cyclotomic_eval`

English:
theorem sub_one_pow_totient_lt_cyclotomic_eval
  given: {n : Nat} {q : Real} (hn' : 2 <= n) (hq' : 1 < q)
  proof: by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : forall ζ' in primitiveRoots n Complex, q - 1 <= ‖↑q - ζ'‖ := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert! norm_sub_norm_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg hq.le]


中文:
定理 sub_one_pow_totient_lt_cyclotomic_eval
  条件: {n : 自然数} {q : 实数} (hn' : 2 <= n) (hq' : 1 < q)
  证明: by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : forall ζ' in primitiveRoots n Complex, q - 1 <= ‖↑q - ζ'‖ := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert! norm_sub_norm_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg hq.le]


Depends on / 依赖: Complex.I, Complex.exp, Complex.isPrimitiveRoot_exp, Complex.norm_real, ContinuousMul, IsPrimitiveRoot, IsStrictOrderedRing, IsStrictOrderedRing.toContinuousInv, Real.norm_of_nonneg, Real.pi, _eq_one, convert, hn.ne, hq.le, isPrimitiveRoot_exp, mem_primitiveRoots, norm_of_nonneg, norm_real, norm_sub_norm_le, pos_of_gt
-/
theorem sub_one_pow_totient_lt_cyclotomic_eval {n : Nat} {q : Real} (hn' : 2 <= n) (hq' : 1 < q) :
    (q - 1) ^ totient n < (cyclotomic n Real).eval q := by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : forall ζ' in primitiveRoots n Complex, q - 1 <= ‖↑q - ζ'‖ := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert! norm_sub_norm_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg hq.le]
    · rw [hζ'.norm'_eq_one hn.ne']
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hex : exists ζ' in primitiveRoots n Complex, q - 1 < ‖↑q - ζ'‖ := by
    refine ⟨ζ, (mem_primitiveRoots hn).mpr hζ, ?_⟩
    suffices ¬SameRay Real (q : Complex) ζ by
      convert! lt_norm_sub_of_not_sameRay this <;>
        simp only [hζ.norm'_eq_one hn.ne', Real.norm_of_nonneg hq.le, Complex.norm_real]
    rw [Complex.sameRay_iff]
    push Not
    refine ⟨mod_cast hq.ne', hζ.ne_zero hn.ne', ?_⟩
    rw [Complex.arg_ofReal_of_nonneg hq.le]; rw [Ne]; rw [eq_comm]; rw [hζ.arg_eq_zero_iff hn.ne']
    clear_value ζ
    rintro rfl
    linarith [hζ.unique IsPrimitiveRoot.one]
  have : ¬eval (↑q) (cyclotomic n Complex) = 0 := by simpa using (cyclotomic_pos' n hq').ne'
  suffices Units.mk0 (Real.toNNReal (q - 1)) (by simp [hq']) ^ totient n <
      Units.mk0 ‖(cyclotomic n Complex).eval ↑q‖₊ (by simp_all) by
    simp only [← Units.val_lt_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← NNReal.coe_lt_coe,
      hq'.le, coe_nnnorm, NNReal.coe_pow, Real.coe_toNNReal', sub_nonneg, sup_of_le_left] at this
    convert! this
    rw [eq_comm]
    simp [cyclotomic_nonneg n hq'.le]
  simp only [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, eval_C, eval_X, eval_sub,
    nnnorm_prod, Units.mk0_prod]
  convert! Finset.prod_lt_prod' (M := NNRealˣ) _ _
  swap; · exact fun _ => Units.mk0 (Real.toNNReal (q - 1)) (by simp [hq'])
  · simp only [Complex.card_primitiveRoots, prod_const, card_attach]
  · simp only [Finset.mem_attach, forall_true_left, Subtype.forall, ←
      Units.val_le_val, ← NNReal.coe_le_coe, norm_nonneg, Units.val_mk0,
      Real.coe_toNNReal', coe_nnnorm, max_le_iff, tsub_le_iff_right]
    intro x hx
    simpa only [and_true, tsub_le_iff_right] using hfor x hx
  · simp only [Finset.mem_attach, Subtype.exists, ←
      NNReal.coe_lt_coe, ← Units.val_lt_val, Units.val_mk0 _, coe_nnnorm]
    simpa [hq'.le, Real.coe_toNNReal', max_eq_left, sub_nonneg] using hex

/--
theorem `sub_one_pow_totient_le_cyclotomic_eval` / 定理 `sub_one_pow_totient_le_cyclotomic_eval`

English:
theorem sub_one_pow_totient_le_cyclotomic_eval
  given: {q : Real} (hq' : 1 < q)

中文:
定理 sub_one_pow_totient_le_cyclotomic_eval
  条件: {q : 实数} (hq' : 1 < q)
-/
theorem sub_one_pow_totient_le_cyclotomic_eval {q : Real} (hq' : 1 < q) :
    forall n, (q - 1) ^ totient n <= (cyclotomic n Real).eval q
  | 0 => by simp only [totient_zero, _root_.pow_zero, cyclotomic_zero, eval_one, le_refl]
  | 1 => by simp only [totient_one, pow_one, cyclotomic_one, eval_sub, eval_X, eval_one, le_refl]
  | _ + 2 => (sub_one_pow_totient_lt_cyclotomic_eval le_add_self hq').le

/--
theorem `cyclotomic_eval_lt_add_one_pow_totient` / 定理 `cyclotomic_eval_lt_add_one_pow_totient`

English:
theorem cyclotomic_eval_lt_add_one_pow_totient
  given: {n : Nat} {q : Real} (hn' : 3 <= n) (hq' : 1 < q)
  proof: by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : forall ζ' in primitiveRoots n Complex, ‖↑q - ζ'‖ <= q + 1 := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert! norm_sub_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg (zero_le_one

中文:
定理 cyclotomic_eval_lt_add_one_pow_totient
  条件: {n : 自然数} {q : 实数} (hn' : 3 <= n) (hq' : 1 < q)
  证明: by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : forall ζ' in primitiveRoots n Complex, ‖↑q - ζ'‖ <= q + 1 := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert! norm_sub_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg (zero_le_one

Depends on / 依赖: Complex.I, Complex.exp, Complex.isPrimitiveRoot_exp, Complex.norm_real, IsPrimitiveRoot, IsStrictOrderedRing, IsStrictOrderedRing.topologicalRing, IsTopologicalRing, Real.norm_of_nonneg, Real.pi, _eq_one, convert, hn.ne, isPrimitiveRoot_exp, mem_primitiveRoots, norm_of_nonneg, norm_real, norm_sub_le, pos_of_gt, primitiveRoots
-/
theorem cyclotomic_eval_lt_add_one_pow_totient {n : Nat} {q : Real} (hn' : 3 <= n) (hq' : 1 < q) :
    (cyclotomic n Real).eval q < (q + 1) ^ totient n := by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : forall ζ' in primitiveRoots n Complex, ‖↑q - ζ'‖ <= q + 1 := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert! norm_sub_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans_lt hq').le]
    · rw [hζ'.norm'_eq_one hn.ne']
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hex : exists ζ' in primitiveRoots n Complex, ‖↑q - ζ'‖ < q + 1 := by
    refine ⟨ζ, (mem_primitiveRoots hn).mpr hζ, ?_⟩
    suffices ¬SameRay Real (q : Complex) (-ζ) by
      convert! norm_add_lt_of_not_sameRay this using 2
      · rw [Complex.norm_real]
        symm
        exact abs_eq_self.mpr hq.le
      · simp [hζ.norm'_eq_one hn.ne']
    rw [Complex.sameRay_iff]
    push Not
refine ⟨mod_cast hq.ne', neg_ne_zero.mpr hζ.ne_zero hn.ne', ?_⟩
    rw [Complex.arg_ofReal_of_nonneg hq.le]; rw [Ne]; rw [eq_comm]
    intro h
    rw [Complex.arg_eq_zero_iff]; rw [Complex.neg_re]; rw [neg_nonneg]; rw [Complex.neg_im]; rw [neg_eq_zero] at h
    have hζ₀ : ζ != 0 := by
      clear_value ζ
      rintro rfl
      exact hn.ne' (hζ.unique IsPrimitiveRoot.zero)
    have : ζ.re < 0 ∧ ζ.im = 0 := ⟨h.1.lt_of_ne ?_, h.2⟩
    · rw [← Complex.arg_eq_pi_iff, hζ.arg_eq_pi_iff hn.ne'] at this
      rw [this] at hζ
      linarith [hζ.unique <| IsPrimitiveRoot.neg_one 0 two_ne_zero.symm]
    · contrapose hζ₀
      apply Complex.ext <;> simp [hζ₀, h.2]
  have : ¬eval (↑q) (cyclotomic n Complex) = 0 := by simpa using (cyclotomic_pos' n hq').ne.symm
  suffices Units.mk0 ‖(cyclotomic n Complex).eval ↑q‖₊ (by simp_all) <
      Units.mk0 (Real.toNNReal (q + 1)) (by simp; linarith) ^ totient n by
    simp only [← Units.val_lt_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← NNReal.coe_lt_coe,
      coe_nnnorm, NNReal.coe_pow,
      Real.coe_toNNReal'] at this
    convert! this using 2
    · rw [eq_comm]
      simp [cyclotomic_nonneg n hq'.le]
    rw [eq_comm]; rw [max_eq_left_iff]
    linarith
  simp only [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, eval_C, eval_X, eval_sub,
    nnnorm_prod, Units.mk0_prod]
  convert! Finset.prod_lt_prod' (M := NNRealˣ) _ _
  swap; · exact fun _ => Units.mk0 (Real.toNNReal (q + 1)) (by positivity)
  · simp [Complex.card_primitiveRoots]
  · simp only [Finset.mem_attach, forall_true_left, Subtype.forall, ←
      Units.val_le_val, ← NNReal.coe_le_coe, Units.val_mk0,
      coe_nnnorm]
    intro x hx
    have : ‖_‖ <= _ := hfor x hx
    simp [this]
  · simp only [Finset.mem_attach, Subtype.exists, ←
      NNReal.coe_lt_coe, ← Units.val_lt_val, Units.val_mk0 _, coe_nnnorm]
    obtain ⟨ζ, hζ, hhζ : ‖_‖ < _⟩ := hex
    exact ⟨ζ, hζ, by simp [hhζ]⟩

/--
theorem `cyclotomic_eval_le_add_one_pow_totient` / 定理 `cyclotomic_eval_le_add_one_pow_totient`

English:
theorem cyclotomic_eval_le_add_one_pow_totient
  given: {q : Real} (hq' : 1 < q)

中文:
定理 cyclotomic_eval_le_add_one_pow_totient
  条件: {q : 实数} (hq' : 1 < q)
-/
theorem cyclotomic_eval_le_add_one_pow_totient {q : Real} (hq' : 1 < q) :
    forall n, (cyclotomic n Real).eval q <= (q + 1) ^ totient n
  | 0 => by simp
  | 1 => by simp [add_assoc, zero_le_one]
  | 2 => by simp
  | _ + 3 => (cyclotomic_eval_lt_add_one_pow_totient le_add_self hq').le

/--
theorem `sub_one_pow_totient_lt_natAbs_cyclotomic_eval` / 定理 `sub_one_pow_totient_lt_natAbs_cyclotomic_eval`

English:
theorem sub_one_pow_totient_lt_natAbs_cyclotomic_eval
  given: {n : Nat} {q : Nat} (hn' : 1 < n) (hq : q != 1)
  proof: by
  rcases hq.lt_or_gt.imp_left Nat.lt_one_iff.mp with (rfl | hq')
  · rw [zero_tsub, zero_pow (Nat.totient_pos.2 (pos_of_gt hn')).ne', pos_iff_ne_zero,
      Int.natAbs_ne_zero, Nat.cast_zero, ← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero _ hn']
    exact one_ne_zero
  rw [← @Nat.cast_lt Real];

中文:
定理 sub_one_pow_totient_lt_natAbs_cyclotomic_eval
  条件: {n : 自然数} {q : 自然数} (hn' : 1 < n) (hq : q != 1)
  证明: by
  rcases hq.lt_or_gt.imp_left Nat.lt_one_iff.mp with (rfl | hq')
  · rw [zero_tsub, zero_pow (Nat.totient_pos.2 (pos_of_gt hn')).ne', pos_iff_ne_zero,
      Int.natAbs_ne_zero, Nat.cast_zero, ← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero _ hn']
    exact one_ne_zero
  rw [← @Nat.cast_lt Real];

Depends on / 依赖: Int.natAbs_ne_zero, Nat.cast_lt, Nat.cast_natAbs, Nat.cast_one, Nat.cast_pow, Nat.cast_sub, Nat.cast_zero, Nat.lt_one_iff.mp, Nat.one_lt_cast, Nat.totient_pos, cast_lt, cast_natAbs, cast_one, cast_pow, cast_sub, cast_zero, coeff_zero_eq_eval_zero, convert, cyclotomic, cyclotomic.eval_apply
-/
theorem sub_one_pow_totient_lt_natAbs_cyclotomic_eval {n : Nat} {q : Nat} (hn' : 1 < n) (hq : q != 1) :
    (q - 1) ^ totient n < ((cyclotomic n Int).eval ↑q).natAbs := by
  rcases hq.lt_or_gt.imp_left Nat.lt_one_iff.mp with (rfl | hq')
  · rw [zero_tsub, zero_pow (Nat.totient_pos.2 (pos_of_gt hn')).ne', pos_iff_ne_zero,
      Int.natAbs_ne_zero, Nat.cast_zero, ← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero _ hn']
    exact one_ne_zero
  rw [← @Nat.cast_lt Real]; rw [Nat.cast_pow]; rw [Nat.cast_sub hq'.le]; rw [Nat.cast_one]; rw [Nat.cast_natAbs]
  refine (sub_one_pow_totient_lt_cyclotomic_eval hn' (Nat.one_lt_cast.2 hq')).trans_le ?_
  convert! (cyclotomic.eval_apply (q : Int) n (algebraMap Int Real)).trans_le (le_abs_self _)
  simp

/--
theorem `sub_one_lt_natAbs_cyclotomic_eval` / 定理 `sub_one_lt_natAbs_cyclotomic_eval`

English:
theorem sub_one_lt_natAbs_cyclotomic_eval
  given: {n : Nat} {q : Nat} (hn' : 1 < n) (hq : q != 1)
  proof: calc
    q - 1 <= (q - 1) ^ totient n := Nat.le_self_pow (Nat.totient_pos.2 <| pos_of_gt hn').ne' _
    _ < ((cyclotomic n Int).eval ↑q).natAbs := sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn' hq

中文:
定理 sub_one_lt_natAbs_cyclotomic_eval
  条件: {n : 自然数} {q : 自然数} (hn' : 1 < n) (hq : q != 1)
  证明: calc
    q - 1 <= (q - 1) ^ totient n := Nat.le_self_pow (Nat.totient_pos.2 <| pos_of_gt hn').ne' _
    _ < ((cyclotomic n Int).eval ↑q).natAbs := sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn' hq

Depends on / 依赖: Nat.le_self_pow, Nat.totient_pos, cyclotomic, le_self_pow, natAbs, pos_of_gt, sub_one_pow_totient_lt_natAbs_cyclotomic_eval, totient, totient_pos
-/
theorem sub_one_lt_natAbs_cyclotomic_eval {n : Nat} {q : Nat} (hn' : 1 < n) (hq : q != 1) :
    q - 1 < ((cyclotomic n Int).eval ↑q).natAbs :=
  calc
    q - 1 <= (q - 1) ^ totient n := Nat.le_self_pow (Nat.totient_pos.2 <| pos_of_gt hn').ne' _
    _ < ((cyclotomic n Int).eval ↑q).natAbs := sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn' hq

end Polynomial
