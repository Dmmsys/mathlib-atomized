/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Devon Tuma
-/
module

public import Mathlib.Algebra.Polynomial.Splits

/-!
# Scaling the roots of a polynomial

This file defines `scaleRoots p s` for a polynomial `p` in one variable and a ring element `s` to
be the polynomial with root `r * s` for each root `r` of `p` and proves some basic results about it.
-/

@[expose] public section


variable {R S A K : Type*}

namespace Polynomial

section Semiring

variable [Semiring R] [Semiring S]

/--
Definition of `scaleRoots` / `scaleRoots` 的定义

English:
definition scaleRoots
  signature: (p : R[X]) (s : R)
  body: ∑ i in p.support, monomial i (p.coeff i * s ^ (p.natDegree - i))

@[simp]

中文:
定义 scaleRoots
  签名: (p : R[X]) (s : R)
  定义体: ∑ i in p.support, monomial i (p.coeff i * s ^ (p.natDegree - i))

@[simp]

Depends on / 依赖: monomial, natDegree, p.coeff, p.natDegree, p.support, support
-/
noncomputable def scaleRoots (p : R[X]) (s : R) : R[X] :=
  ∑ i in p.support, monomial i (p.coeff i * s ^ (p.natDegree - i))

@[simp]
/--
theorem `coeff_scaleRoots` / 定理 `coeff_scaleRoots`

English:
theorem coeff_scaleRoots
  given: (p : R[X]) (s : R) (i : Nat)
  proof: by
  simp +contextual [scaleRoots, coeff_monomial]

中文:
定理 coeff_scaleRoots
  条件: (p : R[X]) (s : R) (i : 自然数)
  证明: by
  simp +contextual [scaleRoots, coeff_monomial]

Depends on / 依赖: coeff_monomial, contextual, scaleRoots
-/
theorem coeff_scaleRoots (p : R[X]) (s : R) (i : Nat) :
    (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i) := by
  simp +contextual [scaleRoots, coeff_monomial]

/--
theorem `coeff_scaleRoots_natDegree` / 定理 `coeff_scaleRoots_natDegree`

English:
theorem coeff_scaleRoots_natDegree
  given: (p : R[X]) (s : R)
  proof: by
  rw [leadingCoeff]; rw [coeff_scaleRoots]; rw [tsub_self]; rw [pow_zero]; rw [mul_one]

@[simp]

中文:
定理 coeff_scaleRoots_natDegree
  条件: (p : R[X]) (s : R)
  证明: by
  rw [leadingCoeff]; rw [coeff_scaleRoots]; rw [tsub_self]; rw [pow_zero]; rw [mul_one]

@[simp]

Depends on / 依赖: coeff_scaleRoots, leadingCoeff, mul_one, pow_zero, tsub_self
-/
theorem coeff_scaleRoots_natDegree (p : R[X]) (s : R) :
    (scaleRoots p s).coeff p.natDegree = p.leadingCoeff := by
  rw [leadingCoeff]; rw [coeff_scaleRoots]; rw [tsub_self]; rw [pow_zero]; rw [mul_one]

@[simp]
/--
theorem `zero_scaleRoots` / 定理 `zero_scaleRoots`

English:
theorem zero_scaleRoots
  given: (s : R)
  statement: scaleRoots 0 s = 0
  proof: by
  ext
  simp

中文:
定理 zero_scaleRoots
  条件: (s : R)
  结论: scaleRoots 0 s = 0
  证明: by
  ext
  simp
-/
theorem zero_scaleRoots (s : R) : scaleRoots 0 s = 0 := by
  ext
  simp

/--
theorem `scaleRoots_ne_zero` / 定理 `scaleRoots_ne_zero`

English:
theorem scaleRoots_ne_zero
  given: {p : R[X]} (hp : p != 0) (s : R)
  statement: scaleRoots p s != 0
  proof: by
  intro h
  have : p.coeff p.natDegree != 0 := mt leadingCoeff_eq_zero.mp hp
  have : (scaleRoots p s).coeff p.natDegree = 0 :=
    congr_fun (congr_arg (coeff : R[X] -> Nat -> R) h) p.natDegree
  rw [coeff_scaleRoots_natDegree] at this
  contradiction

中文:
定理 scaleRoots_ne_zero
  条件: {p : R[X]} (hp : p != 0) (s : R)
  结论: scaleRoots p s != 0
  证明: by
  intro h
  have : p.coeff p.natDegree != 0 := mt leadingCoeff_eq_zero.mp hp
  have : (scaleRoots p s).coeff p.natDegree = 0 :=
    congr_fun (congr_arg (coeff : R[X] -> Nat -> R) h) p.natDegree
  rw [coeff_scaleRoots_natDegree] at this
  contradiction

Depends on / 依赖: coeff_scaleRoots_natDegree, congr_arg, congr_fun, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, natDegree, p.coeff, p.natDegree, scaleRoots
-/
theorem scaleRoots_ne_zero {p : R[X]} (hp : p != 0) (s : R) : scaleRoots p s != 0 := by
  intro h
  have : p.coeff p.natDegree != 0 := mt leadingCoeff_eq_zero.mp hp
  have : (scaleRoots p s).coeff p.natDegree = 0 :=
    congr_fun (congr_arg (coeff : R[X] -> Nat -> R) h) p.natDegree
  rw [coeff_scaleRoots_natDegree] at this
  contradiction

/--
theorem `support_scaleRoots_le` / 定理 `support_scaleRoots_le`

English:
theorem support_scaleRoots_le
  given: (p : R[X]) (s : R)
  statement: (scaleRoots p s).support <= p.support
  proof: by
  intro
  simpa using left_ne_zero_of_mul

中文:
定理 support_scaleRoots_le
  条件: (p : R[X]) (s : R)
  结论: (scaleRoots p s).support <= p.support
  证明: by
  intro
  simpa using left_ne_zero_of_mul

Depends on / 依赖: left_ne_zero_of_mul
-/
theorem support_scaleRoots_le (p : R[X]) (s : R) : (scaleRoots p s).support <= p.support := by
  intro
  simpa using left_ne_zero_of_mul

/--
theorem `support_scaleRoots_eq` / 定理 `support_scaleRoots_eq`

English:
theorem support_scaleRoots_eq
  given: (p : R[X]) {s : R} (hs : s in nonZeroDivisors R)
  proof: le_antisymm (support_scaleRoots_le p s)
    (by intro i
        simp only [coeff_scaleRoots, Polynomial.mem_support_iff]
        intro p_ne_zero ps_zero
        have := (pow_mem hs (p.natDegree - i)).2 _ ps_zero
        contradiction)

@[simp]

中文:
定理 support_scaleRoots_eq
  条件: (p : R[X]) {s : R} (hs : s in nonZeroDivisors R)
  证明: le_antisymm (support_scaleRoots_le p s)
    (by intro i
        simp only [coeff_scaleRoots, Polynomial.mem_support_iff]
        intro p_ne_zero ps_zero
        have := (pow_mem hs (p.natDegree - i)).2 _ ps_zero
        contradiction)

@[simp]

Depends on / 依赖: Polynomial, Polynomial.mem_support_iff, coeff_scaleRoots, le_antisymm, mem_support_iff, natDegree, p.natDegree, p_ne_zero, pow_mem, ps_zero, support_scaleRoots_le
-/
theorem support_scaleRoots_eq (p : R[X]) {s : R} (hs : s in nonZeroDivisors R) :
    (scaleRoots p s).support = p.support :=
  le_antisymm (support_scaleRoots_le p s)
    (by intro i
        simp only [coeff_scaleRoots, Polynomial.mem_support_iff]
        intro p_ne_zero ps_zero
        have := (pow_mem hs (p.natDegree - i)).2 _ ps_zero
        contradiction)

@[simp]
/--
theorem `degree_scaleRoots` / 定理 `degree_scaleRoots`

English:
theorem degree_scaleRoots
  given: (p : R[X]) {s : R}
  statement: degree (scaleRoots p s) = degree p
  proof: by
  have := Classical.propDecidable
  by_cases hp : p = 0
  · rw [hp, zero_scaleRoots]
  refine le_antisymm (Finset.sup_mono (support_scaleRoots_le p s)) (degree_le_degree ?_)
  rw [coeff_scaleRoots_natDegree]
  intro h
  have := leadingCoeff_eq_zero.mp h
  contradiction

@[simp]

中文:
定理 degree_scaleRoots
  条件: (p : R[X]) {s : R}
  结论: degree (scaleRoots p s) = degree p
  证明: by
  have := Classical.propDecidable
  by_cases hp : p = 0
  · rw [hp, zero_scaleRoots]
  refine le_antisymm (Finset.sup_mono (support_scaleRoots_le p s)) (degree_le_degree ?_)
  rw [coeff_scaleRoots_natDegree]
  intro h
  have := leadingCoeff_eq_zero.mp h
  contradiction

@[simp]

Depends on / 依赖: Classical, Classical.propDecidable, Finset, Finset.sup_mono, coeff_scaleRoots_natDegree, degree_le_degree, le_antisymm, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, propDecidable, sup_mono, support_scaleRoots_le, zero_scaleRoots
-/
theorem degree_scaleRoots (p : R[X]) {s : R} : degree (scaleRoots p s) = degree p := by
  have := Classical.propDecidable
  by_cases hp : p = 0
  · rw [hp, zero_scaleRoots]
  refine le_antisymm (Finset.sup_mono (support_scaleRoots_le p s)) (degree_le_degree ?_)
  rw [coeff_scaleRoots_natDegree]
  intro h
  have := leadingCoeff_eq_zero.mp h
  contradiction

@[simp]
/--
theorem `natDegree_scaleRoots` / 定理 `natDegree_scaleRoots`

English:
theorem natDegree_scaleRoots
  given: (p : R[X]) (s : R)
  statement: natDegree (scaleRoots p s) = natDegree p
  proof: by
  simp only [natDegree, degree_scaleRoots]

@[simp]

中文:
定理 natDegree_scaleRoots
  条件: (p : R[X]) (s : R)
  结论: natDegree (scaleRoots p s) = natDegree p
  证明: by
  simp only [natDegree, degree_scaleRoots]

@[simp]

Depends on / 依赖: degree_scaleRoots, natDegree
-/
theorem natDegree_scaleRoots (p : R[X]) (s : R) : natDegree (scaleRoots p s) = natDegree p := by
  simp only [natDegree, degree_scaleRoots]

@[simp]
/--
lemma `leadingCoeff_scaleRoots` / 引理 `leadingCoeff_scaleRoots`

English:
lemma leadingCoeff_scaleRoots
  given: (p : R[X]) (r : R)
  proof: by
  rw [leadingCoeff]; rw [natDegree_scaleRoots]; rw [coeff_scaleRoots_natDegree]

中文:
引理 leadingCoeff_scaleRoots
  条件: (p : R[X]) (r : R)
  证明: by
  rw [leadingCoeff]; rw [natDegree_scaleRoots]; rw [coeff_scaleRoots_natDegree]

Depends on / 依赖: coeff_scaleRoots_natDegree, leadingCoeff, natDegree_scaleRoots
-/
lemma leadingCoeff_scaleRoots (p : R[X]) (r : R) :
    (p.scaleRoots r).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff]; rw [natDegree_scaleRoots]; rw [coeff_scaleRoots_natDegree]

/--
theorem `monic_scaleRoots_iff` / 定理 `monic_scaleRoots_iff`

English:
theorem monic_scaleRoots_iff
  given: {p : R[X]} (s : R)
  statement: Monic (scaleRoots p s) ↔ Monic p
  proof: by
  simp only [Monic, leadingCoeff_scaleRoots]

中文:
定理 monic_scaleRoots_iff
  条件: {p : R[X]} (s : R)
  结论: Monic (scaleRoots p s) ↔ Monic p
  证明: by
  simp only [Monic, leadingCoeff_scaleRoots]

Depends on / 依赖: leadingCoeff_scaleRoots
-/
theorem monic_scaleRoots_iff {p : R[X]} (s : R) : Monic (scaleRoots p s) ↔ Monic p := by
  simp only [Monic, leadingCoeff_scaleRoots]

/--
theorem `map_scaleRoots` / 定理 `map_scaleRoots`

English:
theorem map_scaleRoots
  given: (p : R[X]) (x : R) (f : R ->+* S) (h : f p.leadingCoeff != 0)
  proof: by
  ext
  simp [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h]

@[simp]

中文:
定理 map_scaleRoots
  条件: (p : R[X]) (x : R) (f : R ->+* S) (h : f p.leadingCoeff != 0)
  证明: by
  ext
  simp [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.natDegree_map_of_leadingCoeff_ne_zero, natDegree_map_of_leadingCoeff_ne_zero
-/
theorem map_scaleRoots (p : R[X]) (x : R) (f : R ->+* S) (h : f p.leadingCoeff != 0) :
    (p.scaleRoots x).map f = (p.map f).scaleRoots (f x) := by
  ext
  simp [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h]

@[simp]
/--
lemma `scaleRoots_C` / 引理 `scaleRoots_C`

English:
lemma scaleRoots_C
  given: (r c : R)
  statement: (C c).scaleRoots r = C c
  proof: by
  ext; simp

@[simp]

中文:
引理 scaleRoots_C
  条件: (r c : R)
  结论: (C c).scaleRoots r = C c
  证明: by
  ext; simp

@[simp]
-/
lemma scaleRoots_C (r c : R) : (C c).scaleRoots r = C c := by
  ext; simp

@[simp]
/--
lemma `scaleRoots_one` / 引理 `scaleRoots_one`

English:
lemma scaleRoots_one
  given: (p : R[X])
  proof: by ext; simp

@[simp]

中文:
引理 scaleRoots_one
  条件: (p : R[X])
  证明: by ext; simp

@[simp]
-/
lemma scaleRoots_one (p : R[X]) :
    p.scaleRoots 1 = p := by ext; simp

@[simp]
/--
lemma `scaleRoots_zero` / 引理 `scaleRoots_zero`

English:
lemma scaleRoots_zero
  given: (p : R[X])
  proof: by
  ext n
  simp only [coeff_scaleRoots, tsub_eq_zero_iff_le, zero_pow_eq, mul_ite,
    mul_one, mul_zero, coeff_smul, coeff_X_pow, smul_eq_mul]
  split_ifs with h₁ h₂ h₂
  · subst h₂; rfl
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne h₁ (Ne.symm h₂))
  · exact (h₁ h₂.ge).elim
  · rfl

@[

中文:
引理 scaleRoots_zero
  条件: (p : R[X])
  证明: by
  ext n
  simp only [coeff_scaleRoots, tsub_eq_zero_iff_le, zero_pow_eq, mul_ite,
    mul_one, mul_zero, coeff_smul, coeff_X_pow, smul_eq_mul]
  split_ifs with h₁ h₂ h₂
  · subst h₂; rfl
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne h₁ (Ne.symm h₂))
  · exact (h₁ h₂.ge).elim
  · rfl

@[

Depends on / 依赖: Ne.symm, coeff_X_pow, coeff_eq_zero_of_natDegree_lt, coeff_scaleRoots, coeff_smul, lt_of_le_of_ne, mul_ite, mul_one, mul_zero, smul_eq_mul, split_ifs, tsub_eq_zero_iff_le, zero_pow_eq
-/
lemma scaleRoots_zero (p : R[X]) :
    p.scaleRoots 0 = p.leadingCoeff • X ^ p.natDegree := by
  ext n
  simp only [coeff_scaleRoots, tsub_eq_zero_iff_le, zero_pow_eq, mul_ite,
    mul_one, mul_zero, coeff_smul, coeff_X_pow, smul_eq_mul]
  split_ifs with h₁ h₂ h₂
  · subst h₂; rfl
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne h₁ (Ne.symm h₂))
  · exact (h₁ h₂.ge).elim
  · rfl

@[simp]
/--
lemma `one_scaleRoots` / 引理 `one_scaleRoots`

English:
lemma one_scaleRoots
  given: (r : R)
  proof: by ext; simp

@[simp]

中文:
引理 one_scaleRoots
  条件: (r : R)
  证明: by ext; simp

@[simp]
-/
lemma one_scaleRoots (r : R) :
    (1 : R[X]).scaleRoots r = 1 := by ext; simp

@[simp]
/--
lemma `X_add_C_scaleRoots` / 引理 `X_add_C_scaleRoots`

English:
lemma X_add_C_scaleRoots
  given: (r s : R)
  statement: (X + C r).scaleRoots s = (X + C (r * s))
  proof: by
  nontriviality R
  ext (_ | _ | i) <;> simp

中文:
引理 X_add_C_scaleRoots
  条件: (r s : R)
  结论: (X + C r).scaleRoots s = (X + C (r * s))
  证明: by
  nontriviality R
  ext (_ | _ | i) <;> simp

Depends on / 依赖: nontriviality
-/
lemma X_add_C_scaleRoots (r s : R) : (X + C r).scaleRoots s = (X + C (r * s)) := by
  nontriviality R
  ext (_ | _ | i) <;> simp

end Semiring

section CommSemiring

variable [Semiring S] [CommSemiring R] [Semiring A] [Field K]

/--
theorem `scaleRoots_eval₂_mul_of_commute` / 定理 `scaleRoots_eval₂_mul_of_commute`

English:
theorem scaleRoots_eval₂_mul_of_commute
  statement: {p : S[X]} (f : S ->+* A) (a : A) (s : S)
  proof: by
  calc
    _ = (scaleRoots p s).support.sum fun i =>
          f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i := by
      simp [eval₂_eq_sum, sum_def]
    _ = p.support.sum fun i => f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i :=
      (Finset.sum_subset (support_scaleRoots_le p s

中文:
定理 scaleRoots_eval₂_mul_of_commute
  结论: {p : S[X]} (f : S ->+* A) (a : A) (s : S)
  证明: by
  calc
    _ = (scaleRoots p s).support.sum fun i =>
          f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i := by
      simp [eval₂_eq_sum, sum_def]
    _ = p.support.sum fun i => f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i :=
      (Finset.sum_subset (support_scaleRoots_le p s

Depends on / 依赖: Finset, Finset.sum_congr, Finset.sum_subset, natDegree, p.coeff, p.natDegree, p.support.sum, scaleRoots, simp_, sum_congr, sum_def, sum_subset, support, support.sum, support_scaleRoots_le
-/
theorem scaleRoots_eval₂_mul_of_commute {p : S[X]} (f : S ->+* A) (a : A) (s : S)
    (hsa : Commute (f s) a) (hf : forall s₁ s₂, Commute (f s₁) (f s₂)) :
    eval₂ f (f s * a) (scaleRoots p s) = f s ^ p.natDegree * eval₂ f a p := by
  calc
    _ = (scaleRoots p s).support.sum fun i =>
          f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i := by
      simp [eval₂_eq_sum, sum_def]
    _ = p.support.sum fun i => f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i :=
      (Finset.sum_subset (support_scaleRoots_le p s) fun i _hi hi' => by
        let : coeff p i * s ^ (p.natDegree - i) = 0 := by simpa using hi'
        simp [this])
    _ = p.support.sum fun i : Nat => f (p.coeff i) * f s ^ (p.natDegree - i + i) * a ^ i :=
      (Finset.sum_congr rfl fun i _hi => by
        simp_rw [f.map_mul, f.map_pow, pow_add, hsa.mul_pow, mul_assoc])
    _ = p.support.sum fun i : Nat => f s ^ p.natDegree * (f (p.coeff i) * a ^ i) :=
      Finset.sum_congr rfl fun i hi => by
        rw [mul_assoc]; rw [← map_pow]; rw [(hf _ _).left_comm]; rw [map_pow]; rw [tsub_add_cancel_of_le]
        exact le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
    _ = f s ^ p.natDegree * eval₂ f a p := by simp [← Finset.mul_sum, eval₂_eq_sum, sum_def]

/--
theorem `scaleRoots_eval₂_mul` / 定理 `scaleRoots_eval₂_mul`

English:
theorem scaleRoots_eval₂_mul
  given: {p : S[X]} (f : S ->+* R) (r : R) (s : S)
  proof: scaleRoots_eval₂_mul_of_commute f r s (mul_comm _ _) fun _ _ => mul_comm _ _

中文:
定理 scaleRoots_eval₂_mul
  条件: {p : S[X]} (f : S ->+* R) (r : R) (s : S)
  证明: scaleRoots_eval₂_mul_of_commute f r s (mul_comm _ _) fun _ _ => mul_comm _ _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, IsSelfAdjoint, WithConv, WithConv.ext_iff, eq_comm, ext_iff, mul_comm, star_eq_iff_star_eq
-/
theorem scaleRoots_eval₂_mul {p : S[X]} (f : S ->+* R) (r : R) (s : S) :
    eval₂ f (f s * r) (scaleRoots p s) = f s ^ p.natDegree * eval₂ f r p :=
  scaleRoots_eval₂_mul_of_commute f r s (mul_comm _ _) fun _ _ => mul_comm _ _

/--
theorem `scaleRoots_eval₂_eq_zero` / 定理 `scaleRoots_eval₂_eq_zero`

English:
theorem scaleRoots_eval₂_eq_zero
  given: {p : S[X]} (f : S ->+* R) {r : R} {s : S} (hr : eval₂ f r p = 0)
  proof: by rw [scaleRoots_eval₂_mul, hr, mul_zero]

中文:
定理 scaleRoots_eval₂_eq_zero
  条件: {p : S[X]} (f : S ->+* R) {r : R} {s : S} (hr : eval₂ f r p = 0)
  证明: by rw [scaleRoots_eval₂_mul, hr, mul_zero]

Depends on / 依赖: mul_zero
-/
theorem scaleRoots_eval₂_eq_zero {p : S[X]} (f : S ->+* R) {r : R} {s : S} (hr : eval₂ f r p = 0) :
    eval₂ f (f s * r) (scaleRoots p s) = 0 := by rw [scaleRoots_eval₂_mul, hr, mul_zero]

/--
lemma `scaleRoots_eval_mul` / 引理 `scaleRoots_eval_mul`

English:
lemma scaleRoots_eval_mul
  given: (p : R[X]) (r s : R)
  proof: scaleRoots_eval₂_mul _ _ _

中文:
引理 scaleRoots_eval_mul
  条件: (p : R[X]) (r s : R)
  证明: scaleRoots_eval₂_mul _ _ _
-/
lemma scaleRoots_eval_mul (p : R[X]) (r s : R) :
    eval (s * r) (p.scaleRoots s) = s ^ p.natDegree * eval r p :=
  scaleRoots_eval₂_mul _ _ _

/--
theorem `scaleRoots_aeval_eq_zero` / 定理 `scaleRoots_aeval_eq_zero`

English:
theorem scaleRoots_aeval_eq_zero
  given: [Algebra R A] {p : R[X]} {a : A} {r : R} (ha : aeval a p = 0)
  proof: by
  rw [aeval_def]; rw [scaleRoots_eval₂_mul_of_commute]; rw [← aeval_def]; rw [ha]; rw [mul_zero]
  · apply Algebra.commutes
  · intros; rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

中文:
定理 scaleRoots_aeval_eq_zero
  条件: [代数 R A] {p : R[X]} {a : A} {r : R} (ha : aeval a p = 0)
  证明: by
  rw [aeval_def]; rw [scaleRoots_eval₂_mul_of_commute]; rw [← aeval_def]; rw [ha]; rw [mul_zero]
  · apply Algebra.commutes
  · intros; rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

Depends on / 依赖: Algebra, Algebra.commutes, Commute, SemiconjBy, aeval_def, commutes, intros, map_mul, mul_comm, mul_zero
-/
theorem scaleRoots_aeval_eq_zero [Algebra R A] {p : R[X]} {a : A} {r : R} (ha : aeval a p = 0) :
    aeval (algebraMap R A r * a) (scaleRoots p r) = 0 := by
  rw [aeval_def]; rw [scaleRoots_eval₂_mul_of_commute]; rw [← aeval_def]; rw [ha]; rw [mul_zero]
  · apply Algebra.commutes
  · intros; rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

/--
theorem `scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero` / 定理 `scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero`

English:
theorem scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero
  statement: {p : S[X]} {f : S ->+* K}
  proof: by
  -- if we don't specify the type with `(_ : S)`, the proof is much slower
  nontriviality S using Subsingleton.eq_zero (α := S)
  convert! @scaleRoots_eval₂_eq_zero _ _ _ _ p f _ s hr
  rw [← mul_div_assoc]; rw [mul_comm]; rw [mul_div_cancel_right₀]
  exact map_ne_zero_of_mem_nonZeroDivisors _ h

中文:
定理 scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero
  结论: {p : S[X]} {f : S ->+* K}
  证明: by
  -- if we don't specify the type with `(_ : S)`, the proof is much slower
  nontriviality S using Subsingleton.eq_zero (α := S)
  convert! @scaleRoots_eval₂_eq_zero _ _ _ _ p f _ s hr
  rw [← mul_div_assoc]; rw [mul_comm]; rw [mul_div_cancel_right₀]
  exact map_ne_zero_of_mem_nonZeroDivisors _ h
-/
theorem scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero {p : S[X]} {f : S ->+* K}
    (hf : Function.Injective f) {r s : S} (hr : eval₂ f (f r / f s) p = 0)
    (hs : s in nonZeroDivisors S) : eval₂ f (f r) (scaleRoots p s) = 0 := by
  -- if we don't specify the type with `(_ : S)`, the proof is much slower
  nontriviality S using Subsingleton.eq_zero (α := S)
  convert! @scaleRoots_eval₂_eq_zero _ _ _ _ p f _ s hr
  rw [← mul_div_assoc]; rw [mul_comm]; rw [mul_div_cancel_right₀]
  exact map_ne_zero_of_mem_nonZeroDivisors _ hf hs

/--
theorem `scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero` / 定理 `scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero`

English:
theorem scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero
  statement: [Algebra R K]
  proof: scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

@[simp]

中文:
定理 scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero
  结论: [代数 R K]
  证明: scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

@[simp]
-/
theorem scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero [Algebra R K]
    (inj : Function.Injective (algebraMap R K)) {p : R[X]} {r s : R}
    (hr : aeval (algebraMap R K r / algebraMap R K s) p = 0) (hs : s in nonZeroDivisors R) :
    aeval (algebraMap R K r) (scaleRoots p s) = 0 :=
  scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

@[simp]
/--
lemma `scaleRoots_mul` / 引理 `scaleRoots_mul`

English:
lemma scaleRoots_mul
  given: (p : R[X]) (r s)
  proof: by
  ext; simp [mul_pow, mul_assoc]

中文:
引理 scaleRoots_mul
  条件: (p : R[X]) (r s)
  证明: by
  ext; simp [mul_pow, mul_assoc]

Depends on / 依赖: mul_assoc, mul_pow
-/
lemma scaleRoots_mul (p : R[X]) (r s) :
    p.scaleRoots (r * s) = (p.scaleRoots r).scaleRoots s := by
  ext; simp [mul_pow, mul_assoc]

/--
lemma `mul_scaleRoots` / 引理 `mul_scaleRoots`

English:
lemma mul_scaleRoots
  given: (p q : R[X]) (r : R)
  proof: by
  ext n; simp only [coeff_scaleRoots, coeff_smul, smul_eq_mul]
  trans (∑ x in Finset.antidiagonal n, coeff p x.1 * coeff q x.2) *
    r ^ (natDegree p + natDegree q - n)
  · rw [← coeff_mul]
    cases lt_or_ge (natDegree (p * q)) n with
    | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, 

中文:
引理 mul_scaleRoots
  条件: (p q : R[X]) (r : R)
  证明: by
  ext n; simp only [coeff_scaleRoots, coeff_smul, smul_eq_mul]
  trans (∑ x in Finset.antidiagonal n, coeff p x.1 * coeff q x.2) *
    r ^ (natDegree p + natDegree q - n)
  · rw [← coeff_mul]
    cases lt_or_ge (natDegree (p * q)) n with
    | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, 

Depends on / 依赖: Finset, Finset.antidiagonal, Finset.me, Finset.sum_congr, Finset.sum_mul, add_comm, antidiagonal, coeff_eq_zero_of_natDegree_lt, coeff_mul, coeff_scaleRoots, coeff_smul, lt_or_ge, mul_assoc, mul_comm, mul_zero, natDegree, natDegree_mul_le, pow_add, smul_eq_mul, sum_congr
-/
lemma mul_scaleRoots (p q : R[X]) (r : R) :
    r ^ (natDegree p + natDegree q - natDegree (p * q)) • (p * q).scaleRoots r =
      p.scaleRoots r * q.scaleRoots r := by
  ext n; simp only [coeff_scaleRoots, coeff_smul, smul_eq_mul]
  trans (∑ x in Finset.antidiagonal n, coeff p x.1 * coeff q x.2) *
    r ^ (natDegree p + natDegree q - n)
  · rw [← coeff_mul]
    cases lt_or_ge (natDegree (p * q)) n with
    | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul, mul_zero]
    | inr h =>
      rw [mul_comm]; rw [mul_assoc]; rw [← pow_add]; rw [add_comm]; rw [tsub_add_tsub_cancel natDegree_mul_le h]
  · rw [coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    simp only [Finset.mem_antidiagonal, coeff_scaleRoots, Prod.forall]
    intro a b e
    cases lt_or_ge (natDegree p) a with
    | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul]
    | inr ha =>
      cases lt_or_ge (natDegree q) b with
      | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul, mul_zero]
      | inr hb =>
        simp only [← e, mul_assoc, mul_comm (r ^ (_ - a)), ← pow_add]
        rw [add_comm (_ - _)]; rw [tsub_add_tsub_comm ha hb]

/--
lemma `mul_scaleRoots'` / 引理 `mul_scaleRoots'`

English:
lemma mul_scaleRoots'
  given: (p q : R[X]) (r : R) (h : leadingCoeff p * leadingCoeff q != 0)
  proof: by
  rw [← mul_scaleRoots]; rw [natDegree_mul' h]; rw [tsub_self]; rw [pow_zero]; rw [one_smul]

中文:
引理 mul_scaleRoots'
  条件: (p q : R[X]) (r : R) (h : leadingCoeff p * leadingCoeff q != 0)
  证明: by
  rw [← mul_scaleRoots]; rw [natDegree_mul' h]; rw [tsub_self]; rw [pow_zero]; rw [one_smul]

Depends on / 依赖: mul_scaleRoots, natDegree_mul, one_smul, pow_zero, tsub_self
-/
lemma mul_scaleRoots' (p q : R[X]) (r : R) (h : leadingCoeff p * leadingCoeff q != 0) :
    (p * q).scaleRoots r = p.scaleRoots r * q.scaleRoots r := by
  rw [← mul_scaleRoots]; rw [natDegree_mul' h]; rw [tsub_self]; rw [pow_zero]; rw [one_smul]

/--
lemma `mul_scaleRoots_of_noZeroDivisors` / 引理 `mul_scaleRoots_of_noZeroDivisors`

English:
lemma mul_scaleRoots_of_noZeroDivisors
  given: (p q : R[X]) (r : R) [NoZeroDivisors R]
  proof: by
  by_cases hp : p = 0; · simp [hp]
  by_cases hq : q = 0; · simp [hq]
  apply mul_scaleRoots'
  simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero, hp, hq, or_self, not_false_eq_true]

中文:
引理 mul_scaleRoots_of_noZeroDivisors
  条件: (p q : R[X]) (r : R) [无零因子 R]
  证明: by
  by_cases hp : p = 0; · simp [hp]
  by_cases hq : q = 0; · simp [hq]
  apply mul_scaleRoots'
  simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero, hp, hq, or_self, not_false_eq_true]

Depends on / 依赖: leadingCoeff_eq_zero, mul_eq_zero, mul_scaleRoots, ne_eq, not_false_eq_true, or_self
-/
lemma mul_scaleRoots_of_noZeroDivisors (p q : R[X]) (r : R) [NoZeroDivisors R] :
    (p * q).scaleRoots r = p.scaleRoots r * q.scaleRoots r := by
  by_cases hp : p = 0; · simp [hp]
  by_cases hq : q = 0; · simp [hq]
  apply mul_scaleRoots'
  simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero, hp, hq, or_self, not_false_eq_true]

/--
lemma `pow_scaleRoots'` / 引理 `pow_scaleRoots'`

English:
lemma pow_scaleRoots'
  statement: (p : R[X]) (r : R) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [pow_succ]; rw [mul_scaleRoots']; rw [IH]; rw [pow_succ]
    · refine mt (by simp +contextual [pow_succ]) hp
    · rwa [leadingCoeff_pow' (mt (by simp +contextual [pow_succ]) hp), ← pow_succ]

中文:
引理 pow_scaleRoots'
  结论: (p : R[X]) (r : R) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [pow_succ]; rw [mul_scaleRoots']; rw [IH]; rw [pow_succ]
    · refine mt (by simp +contextual [pow_succ]) hp
    · rwa [leadingCoeff_pow' (mt (by simp +contextual [pow_succ]) hp), ← pow_succ]

Depends on / 依赖: contextual, leadingCoeff_pow, mul_scaleRoots, pow_succ
-/
lemma pow_scaleRoots' (p : R[X]) (r : R) (n : Nat)
    (hp : p.leadingCoeff ^ n != 0) :
    (p ^ n).scaleRoots r = p.scaleRoots r ^ n := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [pow_succ]; rw [mul_scaleRoots']; rw [IH]; rw [pow_succ]
    · refine mt (by simp +contextual [pow_succ]) hp
    · rwa [leadingCoeff_pow' (mt (by simp +contextual [pow_succ]) hp), ← pow_succ]

/--
lemma `pow_scaleRoots_of_isReduced` / 引理 `pow_scaleRoots_of_isReduced`

English:
lemma pow_scaleRoots_of_isReduced
  given: [IsReduced R] (p : R[X]) (r : R) (n : Nat)
  proof: by
  by_cases hp : p = 0
  · simp [hp, zero_pow_eq, apply_ite (scaleRoots · r)]
  by_cases hn : n = 0
  · simp [hn]
  exact pow_scaleRoots' _ _ _ (by simp_all)

中文:
引理 pow_scaleRoots_of_isReduced
  条件: [是既约 R] (p : R[X]) (r : R) (n : 自然数)
  证明: by
  by_cases hp : p = 0
  · simp [hp, zero_pow_eq, apply_ite (scaleRoots · r)]
  by_cases hn : n = 0
  · simp [hn]
  exact pow_scaleRoots' _ _ _ (by simp_all)

Depends on / 依赖: apply_ite, pow_scaleRoots, scaleRoots, zero_pow_eq
-/
lemma pow_scaleRoots_of_isReduced [IsReduced R] (p : R[X]) (r : R) (n : Nat) :
    (p ^ n).scaleRoots r = p.scaleRoots r ^ n := by
  by_cases hp : p = 0
  · simp [hp, zero_pow_eq, apply_ite (scaleRoots · r)]
  by_cases hn : n = 0
  · simp [hn]
  exact pow_scaleRoots' _ _ _ (by simp_all)

/--
lemma `add_scaleRoots_of_natDegree_eq` / 引理 `add_scaleRoots_of_natDegree_eq`

English:
lemma add_scaleRoots_of_natDegree_eq
  given: (p q : R[X]) (r : R) (h : natDegree p = natDegree q)
  proof: by
  ext n; simp only [coeff_smul, coeff_scaleRoots, coeff_add, smul_eq_mul,
    mul_comm (r ^ _), ← h, ← add_mul]
  #adaptation_note /-- v4.7.0-rc1
  Previously `mul_assoc` was part of the `simp only` above, and this `rw` was not needed.
  but this now causes a max rec depth error. -/
  rw [mul_ass

中文:
引理 add_scaleRoots_of_natDegree_eq
  条件: (p q : R[X]) (r : R) (h : natDegree p = natDegree q)
  证明: by
  ext n; simp only [coeff_smul, coeff_scaleRoots, coeff_add, smul_eq_mul,
    mul_comm (r ^ _), ← h, ← add_mul]
  #adaptation_note /-- v4.7.0-rc1
  Previously `mul_assoc` was part of the `simp only` above, and this `rw` was not needed.
  but this now causes a max rec depth error. -/
  rw [mul_ass

Depends on / 依赖: Previously, adaptation_note, add_comm, add_mul, causes, coeff_add, coeff_eq_zero_of_natDegree_lt, coeff_scaleRoots, coeff_smul, lt_or_ge, mul_assoc, mul_comm, natDegree, natDegree_a, needed, pow_add, smul_eq_mul, tsub_add_tsub_cancel, zero_mul
-/
lemma add_scaleRoots_of_natDegree_eq (p q : R[X]) (r : R) (h : natDegree p = natDegree q) :
    r ^ (natDegree p - natDegree (p + q)) • (p + q).scaleRoots r =
      p.scaleRoots r + q.scaleRoots r := by
  ext n; simp only [coeff_smul, coeff_scaleRoots, coeff_add, smul_eq_mul,
    mul_comm (r ^ _), ← h, ← add_mul]
  #adaptation_note /-- v4.7.0-rc1
  Previously `mul_assoc` was part of the `simp only` above, and this `rw` was not needed.
  but this now causes a max rec depth error. -/
  rw [mul_assoc]; rw [← pow_add]
  cases lt_or_ge (natDegree (p + q)) n with
  | inl hn => simp only [← coeff_add, coeff_eq_zero_of_natDegree_lt hn, zero_mul]
  | inr hn =>
      rw [add_comm (_ - n)]; rw [tsub_add_tsub_cancel (natDegree_add_le_of_degree_le le_rfl h.ge) hn]

/--
lemma `scaleRoots_dvd'` / 引理 `scaleRoots_dvd'`

English:
lemma scaleRoots_dvd'
  statement: (p q : R[X]) {r : R} (hr : IsUnit r)
  proof: by
  obtain ⟨a, rfl⟩ := hpq
  rw [← ((hr.pow (natDegree p + natDegree a - natDegree (p * a))).map
    (algebraMap R R[X])).dvd_mul_left, ← Algebra.smul_def, mul_scaleRoots]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)

中文:
引理 scaleRoots_dvd'
  结论: (p q : R[X]) {r : R} (hr : 是单位 r)
  证明: by
  obtain ⟨a, rfl⟩ := hpq
  rw [← ((hr.pow (natDegree p + natDegree a - natDegree (p * a))).map
    (algebraMap R R[X])).dvd_mul_left, ← Algebra.smul_def, mul_scaleRoots]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)

Depends on / 依赖: Algebra, Algebra.smul_def, algebraMap, dvd_mul_left, dvd_mul_right, hr.pow, mul_scaleRoots, natDegree, scaleRoots, smul_def
-/
lemma scaleRoots_dvd' (p q : R[X]) {r : R} (hr : IsUnit r)
    (hpq : p ∣ q) : p.scaleRoots r ∣ q.scaleRoots r := by
  obtain ⟨a, rfl⟩ := hpq
  rw [← ((hr.pow (natDegree p + natDegree a - natDegree (p * a))).map
    (algebraMap R R[X])).dvd_mul_left, ← Algebra.smul_def, mul_scaleRoots]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)

/--
lemma `scaleRoots_dvd` / 引理 `scaleRoots_dvd`

English:
lemma scaleRoots_dvd
  given: (p q : R[X]) {r : R} [NoZeroDivisors R] (hpq : p ∣ q)
  proof: by
  obtain ⟨a, rfl⟩ := hpq
  rw [mul_scaleRoots_of_noZeroDivisors]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)
alias _root_.Dvd.dvd.scaleRoots := scaleRoots_dvd

中文:
引理 scaleRoots_dvd
  条件: (p q : R[X]) {r : R} [无零因子 R] (hpq : p ∣ q)
  证明: by
  obtain ⟨a, rfl⟩ := hpq
  rw [mul_scaleRoots_of_noZeroDivisors]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)
alias _root_.Dvd.dvd.scaleRoots := scaleRoots_dvd

Depends on / 依赖: _root_, _root_.Dvd.dvd.scaleRoots, dvd_mul_right, mul_scaleRoots_of_noZeroDivisors, scaleRoots, scaleRoots_dvd
-/
lemma scaleRoots_dvd (p q : R[X]) {r : R} [NoZeroDivisors R] (hpq : p ∣ q) :
    p.scaleRoots r ∣ q.scaleRoots r := by
  obtain ⟨a, rfl⟩ := hpq
  rw [mul_scaleRoots_of_noZeroDivisors]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)
alias _root_.Dvd.dvd.scaleRoots := scaleRoots_dvd

/--
lemma `scaleRoots_dvd_iff` / 引理 `scaleRoots_dvd_iff`

English:
lemma scaleRoots_dvd_iff
  given: (p q : R[X]) {r : R} (hr : IsUnit r)
  proof: by
  refine ⟨?_ ∘ scaleRoots_dvd' _ _ (hr.unit⁻¹).isUnit, scaleRoots_dvd' p q hr⟩
  simp [← scaleRoots_mul, scaleRoots_one]
alias _root_.IsUnit.scaleRoots_dvd_iff := scaleRoots_dvd_iff

中文:
引理 scaleRoots_dvd_iff
  条件: (p q : R[X]) {r : R} (hr : 是单位 r)
  证明: by
  refine ⟨?_ ∘ scaleRoots_dvd' _ _ (hr.unit⁻¹).isUnit, scaleRoots_dvd' p q hr⟩
  simp [← scaleRoots_mul, scaleRoots_one]
alias _root_.IsUnit.scaleRoots_dvd_iff := scaleRoots_dvd_iff

Depends on / 依赖: IsUnit, _root_, _root_.IsUnit.scaleRoots_dvd_iff, hr.unit, isUnit, scaleRoots_dvd, scaleRoots_dvd_iff, scaleRoots_mul, scaleRoots_one
-/
lemma scaleRoots_dvd_iff (p q : R[X]) {r : R} (hr : IsUnit r) :
    p.scaleRoots r ∣ q.scaleRoots r ↔ p ∣ q := by
  refine ⟨?_ ∘ scaleRoots_dvd' _ _ (hr.unit⁻¹).isUnit, scaleRoots_dvd' p q hr⟩
  simp [← scaleRoots_mul, scaleRoots_one]
alias _root_.IsUnit.scaleRoots_dvd_iff := scaleRoots_dvd_iff

/--
lemma `isCoprime_scaleRoots` / 引理 `isCoprime_scaleRoots`

English:
lemma isCoprime_scaleRoots
  given: (p q : R[X]) (r : R) (hr : IsUnit r) (h : IsCoprime p q)
  proof: by
  obtain ⟨a, b, e⟩ := h
  let s : R := ↑hr.unit⁻¹
  have : natDegree (a * p) = natDegree (b * q) := by
    apply natDegree_eq_of_natDegree_add_eq_zero
    rw [e]; rw [natDegree_one]
  use s ^ natDegree (a * p) • s ^ (natDegree a + natDegree p - natDegree (a * p)) • a.scaleRoots r
  use s ^ natDeg

中文:
引理 isCoprime_scaleRoots
  条件: (p q : R[X]) (r : R) (hr : 是单位 r) (h : IsCoprime p q)
  证明: by
  obtain ⟨a, b, e⟩ := h
  let s : R := ↑hr.unit⁻¹
  have : natDegree (a * p) = natDegree (b * q) := by
    apply natDegree_eq_of_natDegree_add_eq_zero
    rw [e]; rw [natDegree_one]
  use s ^ natDegree (a * p) • s ^ (natDegree a + natDegree p - natDegree (a * p)) • a.scaleRoots r
  use s ^ natDeg

Depends on / 依赖: IsUnit, IsUnit.val_inv_mul, a.scaleRoots, add_s, b.scaleRoots, hr.unit, mul_assoc, mul_one, mul_pow, mul_scaleRoots, natDegree, natDegree_eq_of_natDegree_add_eq_zero, natDegree_one, one_pow, scaleRoots, smul_add, smul_mul_assoc, smul_smul, val_inv_mul
-/
lemma isCoprime_scaleRoots (p q : R[X]) (r : R) (hr : IsUnit r) (h : IsCoprime p q) :
    IsCoprime (p.scaleRoots r) (q.scaleRoots r) := by
  obtain ⟨a, b, e⟩ := h
  let s : R := ↑hr.unit⁻¹
  have : natDegree (a * p) = natDegree (b * q) := by
    apply natDegree_eq_of_natDegree_add_eq_zero
    rw [e]; rw [natDegree_one]
  use s ^ natDegree (a * p) • s ^ (natDegree a + natDegree p - natDegree (a * p)) • a.scaleRoots r
  use s ^ natDegree (a * p) • s ^ (natDegree b + natDegree q - natDegree (b * q)) • b.scaleRoots r
  simp only [smul_smul, smul_mul_assoc, ← mul_scaleRoots, mul_assoc, ← mul_pow, IsUnit.val_inv_mul,
    one_pow, mul_one, ← smul_add, ← add_scaleRoots_of_natDegree_eq _ _ _ this, e, natDegree_one,
    Nat.sub_zero, one_scaleRoots, one_smul, s]

alias _root_.IsCoprime.scaleRoots := isCoprime_scaleRoots

/--
lemma `Splits.scaleRoots` / 引理 `Splits.scaleRoots`

English:
lemma Splits.scaleRoots
  given: {p : R[X]} (hp : p.Splits) (r : R)
  proof: by
  cases subsingleton_or_nontrivial R
  · rwa [Subsingleton.elim (p.scaleRoots r) p]
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hp
  rw [hm]; rw [mul_scaleRoots']; rw [scaleRoots_C]
  · clear hm
    refine .mul (.C _) ?_
    induction m using Mul

中文:
引理 Splits.scaleRoots
  条件: {p : R[X]} (hp : p.Splits) (r : R)
  证明: by
  cases subsingleton_or_nontrivial R
  · rwa [Subsingleton.elim (p.scaleRoots r) p]
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hp
  rw [hm]; rw [mul_scaleRoots']; rw [scaleRoots_C]
  · clear hm
    refine .mul (.C _) ?_
    induction m using Mul

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.prod_cons, Subsingleton, Subsingleton.elim, X_add_C, X_add_C_scaleRoots, eq_or_ne, induction_on, leadingCoeff_X_add_C, map_cons, mul_scaleRoots, one_mu, p.scaleRoots, prod_cons, scaleRoots, scaleRoots_C, splits_iff_exists_multiset, subsingleton_or_nontrivial
-/
lemma Splits.scaleRoots {p : R[X]} (hp : p.Splits) (r : R) :
    (p.scaleRoots r).Splits := by
  cases subsingleton_or_nontrivial R
  · rwa [Subsingleton.elim (p.scaleRoots r) p]
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hp
  rw [hm]; rw [mul_scaleRoots']; rw [scaleRoots_C]
  · clear hm
    refine .mul (.C _) ?_
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a s IH =>
      rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [mul_scaleRoots']; rw [X_add_C_scaleRoots]
      · exact .mul (.X_add_C _) IH
      · simp only [leadingCoeff_X_add_C, one_mul, ne_eq, leadingCoeff_eq_zero]
        exact (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_add_C _).ne_zero
  · rw [(monic_multiset_prod_of_monic _ _ fun a _ => monic_X_add_C _).leadingCoeff]
    simpa

end CommSemiring

section Ring

@[simp]
/--
lemma `X_sub_C_scaleRoots` / 引理 `X_sub_C_scaleRoots`

English:
lemma X_sub_C_scaleRoots
  given: [Ring R] (r s : R)
  proof: by
  nontriviality R
  ext (_ | _ | i) <;> simp

中文:
引理 X_sub_C_scaleRoots
  条件: [环 R] (r s : R)
  证明: by
  nontriviality R
  ext (_ | _ | i) <;> simp

Depends on / 依赖: nontriviality
-/
lemma X_sub_C_scaleRoots [Ring R] (r s : R) :
    (X - C r).scaleRoots s = (X - C (r * s)) := by
  nontriviality R
  ext (_ | _ | i) <;> simp

end Ring

section CommRing

variable [CommRing R]

/--
lemma `rootMultiplicity_scaleRoots` / 引理 `rootMultiplicity_scaleRoots`

English:
lemma rootMultiplicity_scaleRoots
  given: (p : R[X]) {r a : R} (hr : IsLeftRegular r)
  proof: by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0]
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain ⟨q, e, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp a
  have hq0 : q != 0 := by contrapose hp; simp_all
  conv_lhs => rw [e]
  rw [mul_scaleRoots']; rw [pow_scal

中文:
引理 rootMultiplicity_scaleRoots
  条件: (p : R[X]) {r a : R} (hr : IsLeftRegular r)
  证明: by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0]
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain ⟨q, e, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp a
  have hq0 : q != 0 := by contrapose hp; simp_all
  conv_lhs => rw [e]
  rw [mul_scaleRoots']; rw [pow_scal

Depends on / 依赖: IsRoot, IsRoot.def, Nat.add_eq_rig, Subsingleton, Subsingleton.elim, X_sub_C_scaleRoots, add_eq_rig, contrapose, conv_lhs, dvd_iff_isRoot, eq_or_ne, exists_eq_pow_rootMultiplicity_mul_and_not_dvd, mul_comm, mul_scaleRoots, pow_scaleRoots, q.scaleRoots, q.scaleRoots_ne_zero, rootMultiplicity_mul_X_sub_C_pow, scaleRoots, scaleRoots_ne_zero
-/
lemma rootMultiplicity_scaleRoots (p : R[X]) {r a : R} (hr : IsLeftRegular r) :
    rootMultiplicity (r * a) (p.scaleRoots r) = rootMultiplicity a p := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0]
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain ⟨q, e, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp a
  have hq0 : q != 0 := by contrapose hp; simp_all
  conv_lhs => rw [e]
  rw [mul_scaleRoots']; rw [pow_scaleRoots']; rw [X_sub_C_scaleRoots]; rw [mul_comm]; rw [mul_comm _ (q.scaleRoots r)]; rw [rootMultiplicity_mul_X_sub_C_pow (q.scaleRoots_ne_zero hq0 _)]
  · rw [dvd_iff_isRoot, IsRoot.def] at hq
    simp only [Nat.add_eq_right, rootMultiplicity_eq_zero_iff, IsRoot.def]
    rw [mul_comm]; rw [scaleRoots_eval_mul]; rw [(hr.pow q.natDegree).mul_left_eq_zero_iff]
    tauto
  · simp
  · rwa [leadingCoeff_pow' (by simp), leadingCoeff_X_sub_C,
      one_pow, one_mul, ne_eq, leadingCoeff_eq_zero]

/--
lemma `roots_scaleRoots` / 引理 `roots_scaleRoots`

English:
lemma roots_scaleRoots
  given: [IsDomain R] (p : R[X]) {r : R} (hr : IsUnit r)
  proof: by
  classical
  ext a
  have : Function.Bijective (α := R) (r * ·) := IsUnit.isUnit_iff_mulLeft_bijective.mp hr
  obtain ⟨a, rfl⟩ := this.2 a
  simp [Multiset.count_map_eq_count' _ p.roots this.1 a,
    rootMultiplicity_scaleRoots _ hr.isRegular.left]

中文:
引理 roots_scaleRoots
  条件: [是整环 R] (p : R[X]) {r : R} (hr : 是单位 r)
  证明: by
  classical
  ext a
  have : Function.Bijective (α := R) (r * ·) := IsUnit.isUnit_iff_mulLeft_bijective.mp hr
  obtain ⟨a, rfl⟩ := this.2 a
  simp [Multiset.count_map_eq_count' _ p.roots this.1 a,
    rootMultiplicity_scaleRoots _ hr.isRegular.left]

Depends on / 依赖: Bijective, Function, Function.Bijective, IsUnit, IsUnit.isUnit_iff_mulLeft_bijective.mp, Multiset, Multiset.count_map_eq_count, classical, count_map_eq_count, hr.isRegular.left, isRegular, isUnit_iff_mulLeft_bijective, p.roots, rootMultiplicity_scaleRoots
-/
lemma roots_scaleRoots [IsDomain R] (p : R[X]) {r : R} (hr : IsUnit r) :
    (p.scaleRoots r).roots = p.roots.map (r * ·) := by
  classical
  ext a
  have : Function.Bijective (α := R) (r * ·) := IsUnit.isUnit_iff_mulLeft_bijective.mp hr
  obtain ⟨a, rfl⟩ := this.2 a
  simp [Multiset.count_map_eq_count' _ p.roots this.1 a,
    rootMultiplicity_scaleRoots _ hr.isRegular.left]

end CommRing

end Polynomial
