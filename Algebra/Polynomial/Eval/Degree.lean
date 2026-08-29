/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Evaluation of polynomials and degrees

This file contains results on the interaction of `Polynomial.eval` and `Polynomial.degree`.

-/

@[expose] public section

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : Nat}

section Semiring

variable [Semiring R] {p q r : R[X]}

section Eval₂

section

variable [Semiring S] (f : R ->+* S) (x : S)

/--
theorem `eval₂_eq_sum_range` / 定理 `eval₂_eq_sum_range`

English:
theorem eval₂_eq_sum_range
  proof: _root_.trans (congr_arg _ p.as_sum_range)
    (_root_.trans (eval₂_finsetSum f _ _ x) (congr_arg _ (by simp)))

中文:
定理 eval₂_eq_sum_range
  证明: _root_.trans (congr_arg _ p.as_sum_range)
    (_root_.trans (eval₂_finsetSum f _ _ x) (congr_arg _ (by simp)))

Depends on / 依赖: _root_, _root_.trans, as_sum_range, congr_arg, p.as_sum_range
-/
theorem eval₂_eq_sum_range :
    p.eval₂ f x = ∑ i in Finset.range (p.natDegree + 1), f (p.coeff i) * x ^ i :=
  _root_.trans (congr_arg _ p.as_sum_range)
    (_root_.trans (eval₂_finsetSum f _ _ x) (congr_arg _ (by simp)))

/--
theorem `eval₂_eq_sum_range'` / 定理 `eval₂_eq_sum_range'`

English:
theorem eval₂_eq_sum_range'
  given: (f : R ->+* S) {p : R[X]} {n : Nat} (hn : p.natDegree < n) (x : S)
  proof: by
  rw [eval₂_eq_sum]; rw [p.sum_over_range' _ _ hn]
  intro i
  rw [f.map_zero]; rw [zero_mul]

中文:
定理 eval₂_eq_sum_range'
  条件: (f : R ->+* S) {p : R[X]} {n : 自然数} (hn : p.natDegree < n) (x : S)
  证明: by
  rw [eval₂_eq_sum]; rw [p.sum_over_range' _ _ hn]
  intro i
  rw [f.map_zero]; rw [zero_mul]

Depends on / 依赖: f.map_zero, map_zero, p.sum_over_range, sum_over_range, zero_mul
-/
theorem eval₂_eq_sum_range' (f : R ->+* S) {p : R[X]} {n : Nat} (hn : p.natDegree < n) (x : S) :
    eval₂ f x p = ∑ i in Finset.range n, f (p.coeff i) * x ^ i := by
  rw [eval₂_eq_sum]; rw [p.sum_over_range' _ _ hn]
  intro i
  rw [f.map_zero]; rw [zero_mul]

end

end Eval₂

section Eval

variable {x : R}

/--
theorem `eval_eq_sum_range` / 定理 `eval_eq_sum_range`

English:
theorem eval_eq_sum_range
  given: {p : R[X]} (x : R)
  proof: by
  rw [eval_eq_sum]; rw [sum_over_range]; simp

中文:
定理 eval_eq_sum_range
  条件: {p : R[X]} (x : R)
  证明: by
  rw [eval_eq_sum]; rw [sum_over_range]; simp

Depends on / 依赖: eval_eq_sum, sum_over_range
-/
theorem eval_eq_sum_range {p : R[X]} (x : R) :
    p.eval x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
  rw [eval_eq_sum]; rw [sum_over_range]; simp

/--
theorem `eval_eq_sum_range'` / 定理 `eval_eq_sum_range'`

English:
theorem eval_eq_sum_range'
  given: {p : R[X]} {n : Nat} (hn : p.natDegree < n) (x : R)
  proof: by
  rw [eval_eq_sum]; rw [p.sum_over_range' _ _ hn]; simp

中文:
定理 eval_eq_sum_range'
  条件: {p : R[X]} {n : 自然数} (hn : p.natDegree < n) (x : R)
  证明: by
  rw [eval_eq_sum]; rw [p.sum_over_range' _ _ hn]; simp

Depends on / 依赖: eval_eq_sum, p.sum_over_range, sum_over_range
-/
theorem eval_eq_sum_range' {p : R[X]} {n : Nat} (hn : p.natDegree < n) (x : R) :
    p.eval x = ∑ i in Finset.range n, p.coeff i * x ^ i := by
  rw [eval_eq_sum]; rw [p.sum_over_range' _ _ hn]; simp

/--
theorem `eval_monomial_one_add_sub` / 定理 `eval_monomial_one_add_sub`

English:
theorem eval_monomial_one_add_sub
  given: [CommRing S] (d : Nat) (y : S)
  proof: by
  have cast_succ : (d + 1 : S) = ((d.succ : Nat) : S) := by simp only [Nat.cast_succ]
  rw [cast_succ]; rw [eval_monomial]; rw [eval_monomial]; rw [add_comm]; rw [add_pow]
  simp only [one_pow, mul_one, mul_comm (y ^ _) (d.choose _)]
  rw [sum_range_succ]; rw [mul_add]; rw [Nat.choose_self]; rw [

中文:
定理 eval_monomial_one_add_sub
  条件: [交换环 S] (d : 自然数) (y : S)
  证明: by
  have cast_succ : (d + 1 : S) = ((d.succ : Nat) : S) := by simp only [Nat.cast_succ]
  rw [cast_succ]; rw [eval_monomial]; rw [eval_monomial]; rw [add_comm]; rw [add_pow]
  simp only [one_pow, mul_one, mul_comm (y ^ _) (d.choose _)]
  rw [sum_range_succ]; rw [mul_add]; rw [Nat.choose_self]; rw [

Depends on / 依赖: Nat.cast_one, Nat.cast_succ, Nat.cast_zero, Nat.choose_self, add_comm, add_pow, add_sub_cancel_right, add_zero, cast_one, cast_succ, cast_zero, choose_self, d.choose, d.succ, eval_monomial, mul_add, mul_assoc, mul_comm, mul_one, mul_sum
-/
theorem eval_monomial_one_add_sub [CommRing S] (d : Nat) (y : S) :
    eval (1 + y) (monomial d (d + 1 : S)) - eval y (monomial d (d + 1 : S)) =
      ∑ x_1 in range (d + 1), ↑((d + 1).choose x_1) * (↑x_1 * y ^ (x_1 - 1)) := by
  have cast_succ : (d + 1 : S) = ((d.succ : Nat) : S) := by simp only [Nat.cast_succ]
  rw [cast_succ]; rw [eval_monomial]; rw [eval_monomial]; rw [add_comm]; rw [add_pow]
  simp only [one_pow, mul_one, mul_comm (y ^ _) (d.choose _)]
  rw [sum_range_succ]; rw [mul_add]; rw [Nat.choose_self]; rw [Nat.cast_one]; rw [one_mul]; rw [add_sub_cancel_right]; rw [mul_sum]; rw [sum_range_succ']; rw [Nat.cast_zero]; rw [zero_mul]; rw [mul_zero]; rw [add_zero]
  refine sum_congr rfl fun y _hy => ?_
  rw [← mul_assoc]; rw [← mul_assoc]; rw [← Nat.cast_mul]; rw [Nat.add_one_mul_choose_eq]; rw [Nat.cast_mul]; rw [Nat.add_sub_cancel]

end Eval

section Comp

/--
theorem `coeff_comp_degree_mul_degree` / 定理 `coeff_comp_degree_mul_degree`

English:
theorem coeff_comp_degree_mul_degree
  given: (hqd0 : natDegree q != 0)
  proof: by
  rw [comp]; rw [eval₂_def]; rw [coeff_sum]
  refine Eq.trans (Finset.sum_eq_single p.natDegree ?h₀ ?h₁) ?h₂
  case h₂ =>
    simp only [coeff_natDegree, coeff_C_mul, coeff_pow_mul_natDegree]
  case h₀ =>
    intro b hbs hbp
    refine coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt ?_)


中文:
定理 coeff_comp_degree_mul_degree
  条件: (hqd0 : natDegree q != 0)
  证明: by
  rw [comp]; rw [eval₂_def]; rw [coeff_sum]
  refine Eq.trans (Finset.sum_eq_single p.natDegree ?h₀ ?h₁) ?h₂
  case h₂ =>
    simp only [coeff_natDegree, coeff_C_mul, coeff_pow_mul_natDegree]
  case h₀ =>
    intro b hbs hbp
    refine coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt ?_)


Depends on / 依赖: Eq.trans, Finset, Finset.sum_eq_single, coeff_C_mul, coeff_eq_zero_of_natDegree_lt, coeff_natDegree, coeff_pow_mul_natDegree, coeff_sum, contextual, le_natDegree_of_mem_supp, lt_of_le_of_ne, natDegree, natDegree_C, natDegree_mul_le, natDegree_mul_le.trans_lt, natDegree_pow_le, natDegree_pow_le.trans_lt, p.natDegree, sum_eq_single, trans_lt
-/
theorem coeff_comp_degree_mul_degree (hqd0 : natDegree q != 0) :
    coeff (p.comp q) (natDegree p * natDegree q) =
    leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [comp]; rw [eval₂_def]; rw [coeff_sum]
  refine Eq.trans (Finset.sum_eq_single p.natDegree ?h₀ ?h₁) ?h₂
  case h₂ =>
    simp only [coeff_natDegree, coeff_C_mul, coeff_pow_mul_natDegree]
  case h₀ =>
    intro b hbs hbp
    refine coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt ?_)
    rw [natDegree_C]; rw [zero_add]
    refine natDegree_pow_le.trans_lt ?_
    gcongr
    exact lt_of_le_of_ne (le_natDegree_of_mem_supp _ hbs) hbp
  case h₁ =>
    simp +contextual

/--
lemma `comp_C_mul_X_coeff` / 引理 `comp_C_mul_X_coeff`

English:
lemma comp_C_mul_X_coeff
  given: {r : R} {n : Nat}
  proof: by
  simp_rw [comp, eval₂_eq_sum_range, (commute_X _).symm.mul_pow,
    ← C_pow, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n _ fun h => ?_]; rw [if_pos rfl]; rw [mul_one]
  · intro b _ h; simp_rw [if_neg h.symm, mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt, zero_mul]
 

中文:
引理 comp_C_mul_X_coeff
  条件: {r : R} {n : 自然数}
  证明: by
  simp_rw [comp, eval₂_eq_sum_range, (commute_X _).symm.mul_pow,
    ← C_pow, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n _ fun h => ?_]; rw [if_pos rfl]; rw [mul_one]
  · intro b _ h; simp_rw [if_neg h.symm, mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt, zero_mul]
 
-/
@[simp] lemma comp_C_mul_X_coeff {r : R} {n : Nat} :
    (p.comp <| C r * X).coeff n = p.coeff n * r ^ n := by
  simp_rw [comp, eval₂_eq_sum_range, (commute_X _).symm.mul_pow,
    ← C_pow, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n _ fun h => ?_]; rw [if_pos rfl]; rw [mul_one]
  · intro b _ h; simp_rw [if_neg h.symm, mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt, zero_mul]
    rwa [Finset.mem_range_succ_iff, not_le] at h

/--
lemma `comp_C_mul_X_eq_zero_iff` / 引理 `comp_C_mul_X_eq_zero_iff`

English:
lemma comp_C_mul_X_eq_zero_iff
  given: {r : R} (hr : r in nonZeroDivisors R)
  proof: by
  simp_rw [ext_iff]
  refine forall_congr' fun n => ?_
  rw [comp_C_mul_X_coeff]; rw [coeff_zero]; rw [mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hr _)]

中文:
引理 comp_C_mul_X_eq_zero_iff
  条件: {r : R} (hr : r in nonZeroDivisors R)
  证明: by
  simp_rw [ext_iff]
  refine forall_congr' fun n => ?_
  rw [comp_C_mul_X_coeff]; rw [coeff_zero]; rw [mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hr _)]

Depends on / 依赖: coeff_zero, comp_C_mul_X_coeff, ext_iff, forall_congr, mul_right_mem_nonZeroDivisors_eq_zero_iff, pow_mem, simp_rw
-/
lemma comp_C_mul_X_eq_zero_iff {r : R} (hr : r in nonZeroDivisors R) :
    p.comp (C r * X) = 0 ↔ p = 0 := by
  simp_rw [ext_iff]
  refine forall_congr' fun n => ?_
  rw [comp_C_mul_X_coeff]; rw [coeff_zero]; rw [mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hr _)]

end Comp

section Map

variable [Semiring S] {f : R ->+* S} {p : R[X]}

variable (f) in
/-- If `R` and `S` are isomorphic, then so are their polynomial rings. -/
@[simps!]
/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (e : R ≃+* S)
  body: RingEquiv.ofRingHom (mapRingHom (e : R ->+* S)) (mapRingHom (e.symm : S ->+* R)) (by ext; simp)
    (by ext; simp)

中文:
定义 mapEquiv
  签名: (e : R ≃+* S)
  定义体: RingEquiv.ofRingHom (mapRingHom (e : R ->+* S)) (mapRingHom (e.symm : S ->+* R)) (by ext; simp)
    (by ext; simp)

Depends on / 依赖: RingEquiv, RingEquiv.ofRingHom, e.symm, mapRingHom, ofRingHom
-/
def mapEquiv (e : R ≃+* S) : R[X] ≃+* S[X] :=
  RingEquiv.ofRingHom (mapRingHom (e : R ->+* S)) (mapRingHom (e.symm : S ->+* R)) (by ext; simp)
    (by ext; simp)

/--
theorem `map_monic_eq_zero_iff` / 定理 `map_monic_eq_zero_iff`

English:
theorem map_monic_eq_zero_iff
  given: (hp : p.Monic)
  statement: p.map f = 0 ↔ forall x, f x = 0
  proof: ⟨fun hfp x =>
    calc
      f x = f x * f p.leadingCoeff := by simp only [mul_one, hp.leadingCoeff, f.map_one]
      _ = f x * (p.map f).coeff p.natDegree := congr_arg _ (coeff_map _ _).symm
      _ = 0 := by simp only [hfp, mul_zero, coeff_zero],
    fun h => ext fun n => by simp only [h, coeff_ma

中文:
定理 map_monic_eq_zero_iff
  条件: (hp : p.Monic)
  结论: p.map f = 0 ↔ 对任意 x, f x = 0
  证明: ⟨fun hfp x =>
    calc
      f x = f x * f p.leadingCoeff := by simp only [mul_one, hp.leadingCoeff, f.map_one]
      _ = f x * (p.map f).coeff p.natDegree := congr_arg _ (coeff_map _ _).symm
      _ = 0 := by simp only [hfp, mul_zero, coeff_zero],
    fun h => ext fun n => by simp only [h, coeff_ma

Depends on / 依赖: coeff_map, coeff_zero, congr_arg, f.map_one, hp.leadingCoeff, leadingCoeff, map_one, mul_one, mul_zero, natDegree, p.leadingCoeff, p.map, p.natDegree
-/
theorem map_monic_eq_zero_iff (hp : p.Monic) : p.map f = 0 ↔ forall x, f x = 0 :=
  ⟨fun hfp x =>
    calc
      f x = f x * f p.leadingCoeff := by simp only [mul_one, hp.leadingCoeff, f.map_one]
      _ = f x * (p.map f).coeff p.natDegree := congr_arg _ (coeff_map _ _).symm
      _ = 0 := by simp only [hfp, mul_zero, coeff_zero],
    fun h => ext fun n => by simp only [h, coeff_map, coeff_zero]⟩

/--
theorem `map_monic_ne_zero` / 定理 `map_monic_ne_zero`

English:
theorem map_monic_ne_zero
  given: (hp : p.Monic) [Nontrivial S]
  statement: p.map f != 0
  proof: fun h =>
  f.map_one_ne_zero ((map_monic_eq_zero_iff hp).mp h _)

中文:
定理 map_monic_ne_zero
  条件: (hp : p.Monic) [非平凡 S]
  结论: p.map f != 0
  证明: fun h =>
  f.map_one_ne_zero ((map_monic_eq_zero_iff hp).mp h _)
-/
theorem map_monic_ne_zero (hp : p.Monic) [Nontrivial S] : p.map f != 0 := fun h =>
  f.map_one_ne_zero ((map_monic_eq_zero_iff hp).mp h _)

/--
lemma `degree_map_le` / 引理 `degree_map_le`

English:
lemma degree_map_le
  statement: degree (p.map f) <= degree p
  proof: by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

中文:
引理 degree_map_le
  结论: degree (p.map f) <= degree p
  证明: by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

Depends on / 依赖: degree_le_iff_coeff_zero, degree_lt_iff_coeff_zero, le_rfl
-/
lemma degree_map_le : degree (p.map f) <= degree p := by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

/--
lemma `natDegree_map_le` / 引理 `natDegree_map_le`

English:
lemma natDegree_map_le
  statement: natDegree (p.map f) <= natDegree p
  proof: natDegree_le_natDegree degree_map_le

中文:
引理 natDegree_map_le
  结论: natDegree (p.map f) <= natDegree p
  证明: natDegree_le_natDegree degree_map_le

Depends on / 依赖: degree_map_le, natDegree_le_natDegree
-/
lemma natDegree_map_le : natDegree (p.map f) <= natDegree p := natDegree_le_natDegree degree_map_le

/--
lemma `degree_map_lt` / 引理 `degree_map_lt`

English:
lemma degree_map_lt
  given: (hp : f p.leadingCoeff = 0) (hp₀ : p != 0)
  statement: (p.map f).degree < p.degree
  proof: by
  refine degree_map_le.lt_of_ne fun hpq => hp₀ ?_
  rw [leadingCoeff]; rw [← coeff_map]; rw [← natDegree_eq_natDegree hpq]; rw [← leadingCoeff]; rw [leadingCoeff_eq_zero]
    at hp
  rw [← degree_eq_bot]; rw [← hpq]; rw [hp]; rw [degree_zero]

中文:
引理 degree_map_lt
  条件: (hp : f p.leadingCoeff = 0) (hp₀ : p != 0)
  结论: (p.map f).degree < p.degree
  证明: by
  refine degree_map_le.lt_of_ne fun hpq => hp₀ ?_
  rw [leadingCoeff]; rw [← coeff_map]; rw [← natDegree_eq_natDegree hpq]; rw [← leadingCoeff]; rw [leadingCoeff_eq_zero]
    at hp
  rw [← degree_eq_bot]; rw [← hpq]; rw [hp]; rw [degree_zero]

Depends on / 依赖: coeff_map, degree_eq_bot, degree_map_le, degree_map_le.lt_of_ne, degree_zero, leadingCoeff, leadingCoeff_eq_zero, lt_of_ne, natDegree_eq_natDegree
-/
lemma degree_map_lt (hp : f p.leadingCoeff = 0) (hp₀ : p != 0) : (p.map f).degree < p.degree := by
  refine degree_map_le.lt_of_ne fun hpq => hp₀ ?_
  rw [leadingCoeff]; rw [← coeff_map]; rw [← natDegree_eq_natDegree hpq]; rw [← leadingCoeff]; rw [leadingCoeff_eq_zero]
    at hp
  rw [← degree_eq_bot]; rw [← hpq]; rw [hp]; rw [degree_zero]

/--
lemma `natDegree_map_lt` / 引理 `natDegree_map_lt`

English:
lemma natDegree_map_lt
  given: (hp : f p.leadingCoeff = 0) (hp₀ : map f p != 0)
  proof: natDegree_lt_natDegree hp₀ degree_map_lt hp by rintro rfl; simp at hp₀

中文:
引理 natDegree_map_lt
  条件: (hp : f p.leadingCoeff = 0) (hp₀ : map f p != 0)
  证明: natDegree_lt_natDegree hp₀ degree_map_lt hp by rintro rfl; simp at hp₀

Depends on / 依赖: degree_map_lt, natDegree_lt_natDegree
-/
lemma natDegree_map_lt (hp : f p.leadingCoeff = 0) (hp₀ : map f p != 0) :
    (p.map f).natDegree < p.natDegree :=
natDegree_lt_natDegree hp₀ degree_map_lt hp by rintro rfl; simp at hp₀

/--
lemma `natDegree_map_lt'` / 引理 `natDegree_map_lt'`

English:
lemma natDegree_map_lt'
  given: (hp : f p.leadingCoeff = 0) (hp₀ : 0 < natDegree p)
  proof: by
  by_cases H : map f p = 0
  · rwa [H, natDegree_zero]
  · exact natDegree_map_lt hp H

中文:
引理 natDegree_map_lt'
  条件: (hp : f p.leadingCoeff = 0) (hp₀ : 0 < natDegree p)
  证明: by
  by_cases H : map f p = 0
  · rwa [H, natDegree_zero]
  · exact natDegree_map_lt hp H

Depends on / 依赖: natDegree_map_lt, natDegree_zero
-/
lemma natDegree_map_lt' (hp : f p.leadingCoeff = 0) (hp₀ : 0 < natDegree p) :
    (p.map f).natDegree < p.natDegree := by
  by_cases H : map f p = 0
  · rwa [H, natDegree_zero]
  · exact natDegree_map_lt hp H

/--
theorem `degree_map_eq_of_leadingCoeff_ne_zero` / 定理 `degree_map_eq_of_leadingCoeff_ne_zero`

English:
theorem degree_map_eq_of_leadingCoeff_ne_zero
  given: (f : R ->+* S) (hf : f (leadingCoeff p) != 0)
  proof: by
  refine degree_map_le.antisymm ?_
  have hp0 : p != 0 :=
    leadingCoeff_ne_zero.mp fun hp0 => hf (_root_.trans (congr_arg _ hp0) f.map_zero)
  rw [degree_eq_natDegree hp0]
  refine le_degree_of_ne_zero ?_
  rw [coeff_map]
  exact hf

中文:
定理 degree_map_eq_of_leadingCoeff_ne_zero
  条件: (f : R ->+* S) (hf : f (leadingCoeff p) != 0)
  证明: by
  refine degree_map_le.antisymm ?_
  have hp0 : p != 0 :=
    leadingCoeff_ne_zero.mp fun hp0 => hf (_root_.trans (congr_arg _ hp0) f.map_zero)
  rw [degree_eq_natDegree hp0]
  refine le_degree_of_ne_zero ?_
  rw [coeff_map]
  exact hf

Depends on / 依赖: _root_, _root_.trans, antisymm, coeff_map, congr_arg, degree_eq_natDegree, degree_map_le, degree_map_le.antisymm, f.map_zero, le_degree_of_ne_zero, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mp, map_zero
-/
theorem degree_map_eq_of_leadingCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) :
    degree (p.map f) = degree p := by
  refine degree_map_le.antisymm ?_
  have hp0 : p != 0 :=
    leadingCoeff_ne_zero.mp fun hp0 => hf (_root_.trans (congr_arg _ hp0) f.map_zero)
  rw [degree_eq_natDegree hp0]
  refine le_degree_of_ne_zero ?_
  rw [coeff_map]
  exact hf

/--
theorem `natDegree_map_of_leadingCoeff_ne_zero` / 定理 `natDegree_map_of_leadingCoeff_ne_zero`

English:
theorem natDegree_map_of_leadingCoeff_ne_zero
  given: (f : R ->+* S) (hf : f (leadingCoeff p) != 0)
  proof: natDegree_eq_of_degree_eq (degree_map_eq_of_leadingCoeff_ne_zero f hf)

中文:
定理 natDegree_map_of_leadingCoeff_ne_zero
  条件: (f : R ->+* S) (hf : f (leadingCoeff p) != 0)
  证明: natDegree_eq_of_degree_eq (degree_map_eq_of_leadingCoeff_ne_zero f hf)

Depends on / 依赖: degree_map_eq_of_leadingCoeff_ne_zero, natDegree_eq_of_degree_eq
-/
theorem natDegree_map_of_leadingCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) :
    natDegree (p.map f) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_map_eq_of_leadingCoeff_ne_zero f hf)

/--
theorem `leadingCoeff_map_of_leadingCoeff_ne_zero` / 定理 `leadingCoeff_map_of_leadingCoeff_ne_zero`

English:
theorem leadingCoeff_map_of_leadingCoeff_ne_zero
  given: (f : R ->+* S) (hf : f (leadingCoeff p) != 0)
  proof: by
  unfold leadingCoeff
  rw [coeff_map]; rw [natDegree_map_of_leadingCoeff_ne_zero f hf]

中文:
定理 leadingCoeff_map_of_leadingCoeff_ne_zero
  条件: (f : R ->+* S) (hf : f (leadingCoeff p) != 0)
  证明: by
  unfold leadingCoeff
  rw [coeff_map]; rw [natDegree_map_of_leadingCoeff_ne_zero f hf]

Depends on / 依赖: coeff_map, leadingCoeff, natDegree_map_of_leadingCoeff_ne_zero
-/
theorem leadingCoeff_map_of_leadingCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) :
    leadingCoeff (p.map f) = f (leadingCoeff p) := by
  unfold leadingCoeff
  rw [coeff_map]; rw [natDegree_map_of_leadingCoeff_ne_zero f hf]

/--
theorem `nextCoeff_map_of_leadingCoeff_ne_zero` / 定理 `nextCoeff_map_of_leadingCoeff_ne_zero`

English:
theorem nextCoeff_map_of_leadingCoeff_ne_zero
  given: (f : R ->+* S) (hf : f p.leadingCoeff != 0)
  proof: by
  grind [nextCoeff, natDegree_map_of_leadingCoeff_ne_zero, coeff_map]

中文:
定理 nextCoeff_map_of_leadingCoeff_ne_zero
  条件: (f : R ->+* S) (hf : f p.leadingCoeff != 0)
  证明: by
  grind [nextCoeff, natDegree_map_of_leadingCoeff_ne_zero, coeff_map]

Depends on / 依赖: coeff_map, natDegree_map_of_leadingCoeff_ne_zero, nextCoeff
-/
theorem nextCoeff_map_of_leadingCoeff_ne_zero (f : R ->+* S) (hf : f p.leadingCoeff != 0) :
    (p.map f).nextCoeff = f p.nextCoeff := by
  grind [nextCoeff, natDegree_map_of_leadingCoeff_ne_zero, coeff_map]

end Map

end Semiring

section CommSemiring

section Eval

section

variable [Semiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R ->+* S)

/--
theorem `eval₂_comp` / 定理 `eval₂_comp`

English:
theorem eval₂_comp
  given: {x : S}
  statement: eval₂ f x (p.comp q) = eval₂ f (eval₂ f x q) p
  proof: by
  rw [comp]; rw [p.as_sum_range]; simp [eval₂_finsetSum, eval₂_pow]

@[simp]

中文:
定理 eval₂_comp
  条件: {x : S}
  结论: eval₂ f x (p.comp q) = eval₂ f (eval₂ f x q) p
  证明: by
  rw [comp]; rw [p.as_sum_range]; simp [eval₂_finsetSum, eval₂_pow]

@[simp]

Depends on / 依赖: as_sum_range, p.as_sum_range
-/
theorem eval₂_comp {x : S} : eval₂ f x (p.comp q) = eval₂ f (eval₂ f x q) p := by
  rw [comp]; rw [p.as_sum_range]; simp [eval₂_finsetSum, eval₂_pow]

@[simp]
/--
theorem `iterate_comp_eval₂` / 定理 `iterate_comp_eval₂`

English:
theorem iterate_comp_eval₂
  given: (k : Nat) (t : S)
  proof: by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', eval₂_comp, IH]

中文:
定理 iterate_comp_eval₂
  条件: (k : 自然数) (t : S)
  证明: by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', eval₂_comp, IH]

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply
-/
theorem iterate_comp_eval₂ (k : Nat) (t : S) :
    eval₂ f t (p.comp^[k] q) = (fun x => eval₂ f x p)^[k] (eval₂ f t q) := by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', eval₂_comp, IH]

end

section

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R ->+* S)

@[simp]
/--
theorem `iterate_comp_eval` / 定理 `iterate_comp_eval`

English:
theorem iterate_comp_eval
  proof: iterate_comp_eval₂ _

中文:
定理 iterate_comp_eval
  证明: iterate_comp_eval₂ _
-/
theorem iterate_comp_eval :
    forall (k : Nat) (t : R), (p.comp^[k] q).eval t = (fun x => p.eval x)^[k] (q.eval t) :=
  iterate_comp_eval₂ _

end

end Eval

end CommSemiring

section
variable [Semiring R] [CommRing S] [IsDomain S] (φ : R ->+* S) {f : R[X]}

/--
lemma `isUnit_of_isUnit_leadingCoeff_of_isUnit_map` / 引理 `isUnit_of_isUnit_leadingCoeff_of_isUnit_map`

English:
lemma isUnit_of_isUnit_leadingCoeff_of_isUnit_map
  statement: (hf : IsUnit f.leadingCoeff)
  proof: by
  have dz := degree_eq_zero_of_isUnit H
  rw [degree_map_eq_of_leadingCoeff_ne_zero] at dz
  · rw [eq_C_of_degree_eq_zero dz]
    refine IsUnit.map C ?_
    convert! hf
    change coeff f 0 = coeff f (natDegree f)
    rw [(degree_eq_iff_natDegree_eq _).1 dz]
    · rfl
    rintro rfl
    simp at H

中文:
引理 isUnit_of_isUnit_leadingCoeff_of_isUnit_map
  结论: (hf : 是单位 f.leadingCoeff)
  证明: by
  have dz := degree_eq_zero_of_isUnit H
  rw [degree_map_eq_of_leadingCoeff_ne_zero] at dz
  · rw [eq_C_of_degree_eq_zero dz]
    refine IsUnit.map C ?_
    convert! hf
    change coeff f 0 = coeff f (natDegree f)
    rw [(degree_eq_iff_natDegree_eq _).1 dz]
    · rfl
    rintro rfl
    simp at H

Depends on / 依赖: IsUnit, IsUnit.map, convert, degree_eq_iff_natDegree_eq, degree_eq_zero_of_isUnit, degree_map_eq_of_leadingCoeff_ne_zero, eq_C_of_degree_eq_zero, f.leadingCoeff, leadingCoeff, natDegree
-/
lemma isUnit_of_isUnit_leadingCoeff_of_isUnit_map (hf : IsUnit f.leadingCoeff)
    (H : IsUnit (map φ f)) : IsUnit f := by
  have dz := degree_eq_zero_of_isUnit H
  rw [degree_map_eq_of_leadingCoeff_ne_zero] at dz
  · rw [eq_C_of_degree_eq_zero dz]
    refine IsUnit.map C ?_
    convert! hf
    change coeff f 0 = coeff f (natDegree f)
    rw [(degree_eq_iff_natDegree_eq _).1 dz]
    · rfl
    rintro rfl
    simp at H
  · intro h
    have u : IsUnit (φ f.leadingCoeff) := IsUnit.map φ hf
    rw [h] at u
    simp at u

end

end Polynomial
