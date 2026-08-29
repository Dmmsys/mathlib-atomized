/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Andrew Yang, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Theory of monic polynomials

We define `integralNormalization`, which relate arbitrary polynomials to monic ones.
-/

@[expose] public section


open Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : Nat} {ι : Type y}

section IntegralNormalization

section Semiring

variable [Semiring R]

/--
Definition of `integralNormalization` / `integralNormalization` 的定义

English:
definition integralNormalization
  signature: (p : R[X])
  body: p.sum fun i a =>
    monomial i (if p.degree = i then 1 else a * p.leadingCoeff ^ (p.natDegree - 1 - i))

@[simp]

中文:
定义 integralNormalization
  签名: (p : R[X])
  定义体: p.sum fun i a =>
    monomial i (if p.degree = i then 1 else a * p.leadingCoeff ^ (p.natDegree - 1 - i))

@[simp]

Depends on / 依赖: degree, leadingCoeff, monomial, natDegree, p.degree, p.leadingCoeff, p.natDegree, p.sum
-/
noncomputable def integralNormalization (p : R[X]) : R[X] :=
  p.sum fun i a =>
    monomial i (if p.degree = i then 1 else a * p.leadingCoeff ^ (p.natDegree - 1 - i))

@[simp]
/--
theorem `integralNormalization_zero` / 定理 `integralNormalization_zero`

English:
theorem integralNormalization_zero
  statement: integralNormalization (0 : R[X]) = 0
  proof: by
  simp [integralNormalization]

@[simp]

中文:
定理 integralNormalization_zero
  结论: integralNormalization (0 : R[X]) = 0
  证明: by
  simp [integralNormalization]

@[simp]

Depends on / 依赖: integralNormalization
-/
theorem integralNormalization_zero : integralNormalization (0 : R[X]) = 0 := by
  simp [integralNormalization]

@[simp]
/--
theorem `integralNormalization_C` / 定理 `integralNormalization_C`

English:
theorem integralNormalization_C
  given: {x : R} (hx : x != 0)
  statement: integralNormalization (C x) = 1
  proof: by
  simp [integralNormalization, sum_def, support_C hx, degree_C hx]

中文:
定理 integralNormalization_C
  条件: {x : R} (hx : x != 0)
  结论: integralNormalization (C x) = 1
  证明: by
  simp [integralNormalization, sum_def, support_C hx, degree_C hx]

Depends on / 依赖: degree_C, integralNormalization, sum_def, support_C
-/
theorem integralNormalization_C {x : R} (hx : x != 0) : integralNormalization (C x) = 1 := by
  simp [integralNormalization, sum_def, support_C hx, degree_C hx]

variable {p : R[X]}

/--
theorem `integralNormalization_coeff` / 定理 `integralNormalization_coeff`

English:
theorem integralNormalization_coeff
  given: {i : Nat}
  proof: by
  have : p.coeff i = 0 -> p.degree != i := fun hc hd => coeff_ne_zero_of_eq_degree hd hc
  simp +contextual [sum_def, integralNormalization, coeff_monomial, this,
    mem_support_iff]

中文:
定理 integralNormalization_coeff
  条件: {i : 自然数}
  证明: by
  have : p.coeff i = 0 -> p.degree != i := fun hc hd => coeff_ne_zero_of_eq_degree hd hc
  simp +contextual [sum_def, integralNormalization, coeff_monomial, this,
    mem_support_iff]

Depends on / 依赖: coeff_monomial, coeff_ne_zero_of_eq_degree, contextual, degree, integralNormalization, mem_support_iff, p.coeff, p.degree, sum_def
-/
theorem integralNormalization_coeff {i : Nat} :
    (integralNormalization p).coeff i =
      if p.degree = i then 1 else coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i) := by
  have : p.coeff i = 0 -> p.degree != i := fun hc hd => coeff_ne_zero_of_eq_degree hd hc
  simp +contextual [sum_def, integralNormalization, coeff_monomial, this,
    mem_support_iff]

/--
theorem `support_integralNormalization_subset` / 定理 `support_integralNormalization_subset`

English:
theorem support_integralNormalization_subset
  proof: by
  intro
  simp +contextual [sum_def, integralNormalization, coeff_monomial, mem_support_iff]

中文:
定理 support_integralNormalization_subset
  证明: by
  intro
  simp +contextual [sum_def, integralNormalization, coeff_monomial, mem_support_iff]

Depends on / 依赖: coeff_monomial, contextual, integralNormalization, mem_support_iff, sum_def
-/
theorem support_integralNormalization_subset :
    (integralNormalization p).support subseteq p.support := by
  intro
  simp +contextual [sum_def, integralNormalization, coeff_monomial, mem_support_iff]

/--
theorem `integralNormalization_coeff_degree` / 定理 `integralNormalization_coeff_degree`

English:
theorem integralNormalization_coeff_degree
  given: {i : Nat} (hi : p.degree = i)
  proof: by rw [integralNormalization_coeff, if_pos hi]

中文:
定理 integralNormalization_coeff_degree
  条件: {i : 自然数} (hi : p.degree = i)
  证明: by rw [integralNormalization_coeff, if_pos hi]

Depends on / 依赖: if_pos, integralNormalization_coeff
-/
theorem integralNormalization_coeff_degree {i : Nat} (hi : p.degree = i) :
    (integralNormalization p).coeff i = 1 := by rw [integralNormalization_coeff, if_pos hi]

/--
theorem `integralNormalization_coeff_natDegree` / 定理 `integralNormalization_coeff_natDegree`

English:
theorem integralNormalization_coeff_natDegree
  given: (hp : p != 0)
  proof: integralNormalization_coeff_degree (degree_eq_natDegree hp)

中文:
定理 integralNormalization_coeff_natDegree
  条件: (hp : p != 0)
  证明: integralNormalization_coeff_degree (degree_eq_natDegree hp)

Depends on / 依赖: degree_eq_natDegree, integralNormalization_coeff_degree
-/
theorem integralNormalization_coeff_natDegree (hp : p != 0) :
    (integralNormalization p).coeff (natDegree p) = 1 :=
  integralNormalization_coeff_degree (degree_eq_natDegree hp)

/--
theorem `integralNormalization_coeff_degree_ne` / 定理 `integralNormalization_coeff_degree_ne`

English:
theorem integralNormalization_coeff_degree_ne
  given: {i : Nat} (hi : p.degree != i)
  proof: by
  rw [integralNormalization_coeff]; rw [if_neg hi]

中文:
定理 integralNormalization_coeff_degree_ne
  条件: {i : 自然数} (hi : p.degree != i)
  证明: by
  rw [integralNormalization_coeff]; rw [if_neg hi]

Depends on / 依赖: if_neg, integralNormalization_coeff
-/
theorem integralNormalization_coeff_degree_ne {i : Nat} (hi : p.degree != i) :
    coeff (integralNormalization p) i = coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i) := by
  rw [integralNormalization_coeff]; rw [if_neg hi]

/--
theorem `integralNormalization_coeff_ne_natDegree` / 定理 `integralNormalization_coeff_ne_natDegree`

English:
theorem integralNormalization_coeff_ne_natDegree
  given: {i : Nat} (hi : i != natDegree p)
  proof: integralNormalization_coeff_degree_ne (degree_ne_of_natDegree_ne hi.symm)

@[simp]

中文:
定理 integralNormalization_coeff_ne_natDegree
  条件: {i : 自然数} (hi : i != natDegree p)
  证明: integralNormalization_coeff_degree_ne (degree_ne_of_natDegree_ne hi.symm)

@[simp]

Depends on / 依赖: degree_ne_of_natDegree_ne, hi.symm, integralNormalization_coeff_degree_ne
-/
theorem integralNormalization_coeff_ne_natDegree {i : Nat} (hi : i != natDegree p) :
    coeff (integralNormalization p) i = coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i) :=
  integralNormalization_coeff_degree_ne (degree_ne_of_natDegree_ne hi.symm)

@[simp]
/--
lemma `degree_integralNormalization` / 引理 `degree_integralNormalization`

English:
lemma degree_integralNormalization
  statement: p.integralNormalization.degree = p.degree
  proof: by
  nontriviality R
  by_cases hp : p = 0; · simp [hp]
  rw [degree_eq_natDegree hp]
  refine degree_eq_of_le_of_coeff_ne_zero ?_ (by simp [integralNormalization_coeff_natDegree, *])
  exact (Finset.sup_le fun i h =>
WithBot.coe_le_coe.2 le_natDegree_of_mem_supp i support_integralNormalization_subs

中文:
引理 degree_integralNormalization
  结论: p.integralNormalization.degree = p.degree
  证明: by
  nontriviality R
  by_cases hp : p = 0; · simp [hp]
  rw [degree_eq_natDegree hp]
  refine degree_eq_of_le_of_coeff_ne_zero ?_ (by simp [integralNormalization_coeff_natDegree, *])
  exact (Finset.sup_le fun i h =>
WithBot.coe_le_coe.2 le_natDegree_of_mem_supp i support_integralNormalization_subs

Depends on / 依赖: Finset, Finset.sup_le, WithBot, WithBot.coe_le_coe, coe_le_coe, degree_eq_natDegree, degree_eq_of_le_of_coeff_ne_zero, integralNormalization_coeff_natDegree, le_natDegree_of_mem_supp, nontriviality, sup_le, support_integralNormalization_subset
-/
lemma degree_integralNormalization : p.integralNormalization.degree = p.degree := by
  nontriviality R
  by_cases hp : p = 0; · simp [hp]
  rw [degree_eq_natDegree hp]
  refine degree_eq_of_le_of_coeff_ne_zero ?_ (by simp [integralNormalization_coeff_natDegree, *])
  exact (Finset.sup_le fun i h =>
WithBot.coe_le_coe.2 le_natDegree_of_mem_supp i support_integralNormalization_subset h)

@[simp]
/--
lemma `natDegree_integralNormalization` / 引理 `natDegree_integralNormalization`

English:
lemma natDegree_integralNormalization
  statement: p.integralNormalization.natDegree = p.natDegree
  proof: by
  nontriviality R
  by_cases hp : p = 0; · simp [hp]
  exact natDegree_eq_of_degree_eq p.degree_integralNormalization

中文:
引理 natDegree_integralNormalization
  结论: p.integralNormalization.natDegree = p.natDegree
  证明: by
  nontriviality R
  by_cases hp : p = 0; · simp [hp]
  exact natDegree_eq_of_degree_eq p.degree_integralNormalization

Depends on / 依赖: degree_integralNormalization, natDegree_eq_of_degree_eq, nontriviality, p.degree_integralNormalization
-/
lemma natDegree_integralNormalization : p.integralNormalization.natDegree = p.natDegree := by
  nontriviality R
  by_cases hp : p = 0; · simp [hp]
  exact natDegree_eq_of_degree_eq p.degree_integralNormalization

/--
theorem `monic_integralNormalization` / 定理 `monic_integralNormalization`

English:
theorem monic_integralNormalization
  given: (hp : p != 0)
  statement: Monic (integralNormalization p)
  proof: monic_of_degree_le p.natDegree
    (Finset.sup_le fun i h =>
WithBot.coe_le_coe.2 le_natDegree_of_mem_supp i support_integralNormalization_subset h)
    (integralNormalization_coeff_natDegree hp)

中文:
定理 monic_integralNormalization
  条件: (hp : p != 0)
  结论: Monic (integralNormalization p)
  证明: monic_of_degree_le p.natDegree
    (Finset.sup_le fun i h =>
WithBot.coe_le_coe.2 le_natDegree_of_mem_supp i support_integralNormalization_subset h)
    (integralNormalization_coeff_natDegree hp)

Depends on / 依赖: Finset, Finset.sup_le, WithBot, WithBot.coe_le_coe, coe_le_coe, integralNormalization_coeff_natDegree, le_natDegree_of_mem_supp, monic_of_degree_le, natDegree, p.natDegree, sup_le, support_integralNormalization_subset
-/
theorem monic_integralNormalization (hp : p != 0) : Monic (integralNormalization p) :=
  monic_of_degree_le p.natDegree
    (Finset.sup_le fun i h =>
WithBot.coe_le_coe.2 le_natDegree_of_mem_supp i support_integralNormalization_subset h)
    (integralNormalization_coeff_natDegree hp)

/--
theorem `integralNormalization_coeff_mul_leadingCoeff_pow` / 定理 `integralNormalization_coeff_mul_leadingCoeff_pow`

English:
theorem integralNormalization_coeff_mul_leadingCoeff_pow
  given: (i : Nat) (hp : 1 <= natDegree p)
  proof: by
  rw [integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff,
      ← pow_succ', tsub_add_cancel_of_le (natDegree_eq_of_degree_eq_some h ▸ hp)]
  · simp only [mul_assoc, ← pow_add]
    by_cases h' : i < p.degree
    · rw [tsub_add_cancel_of_le]
  

中文:
定理 integralNormalization_coeff_mul_leadingCoeff_pow
  条件: (i : 自然数) (hp : 1 <= natDegree p)
  证明: by
  rw [integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff,
      ← pow_succ', tsub_add_cancel_of_le (natDegree_eq_of_degree_eq_some h ▸ hp)]
  · simp only [mul_assoc, ← pow_add]
    by_cases h' : i < p.degree
    · rw [tsub_add_cancel_of_le]
  

Depends on / 依赖: Nat.succ_le_iff, coe_lt_degree, coe_lt_degree.mp, coeff_eq_zero_of_degree_lt, degree, integralNormalization_coeff, le_of_not_gt, le_tsub_iff_right, leadingCoeff, lt_of_le_of_ne, mul_assoc, natDegree_eq_of_degree_eq_some, p.degree, pow_add, pow_succ, split_ifs, succ_le_iff, tsub_add_cancel_of_le
-/
theorem integralNormalization_coeff_mul_leadingCoeff_pow (i : Nat) (hp : 1 <= natDegree p) :
    (integralNormalization p).coeff i * p.leadingCoeff ^ i =
      p.coeff i * p.leadingCoeff ^ (p.natDegree - 1) := by
  rw [integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff,
      ← pow_succ', tsub_add_cancel_of_le (natDegree_eq_of_degree_eq_some h ▸ hp)]
  · simp only [mul_assoc, ← pow_add]
    by_cases h' : i < p.degree
    · rw [tsub_add_cancel_of_le]
      rw [le_tsub_iff_right hp]; rw [Nat.succ_le_iff]
      exact coe_lt_degree.mp h'
    · simp [coeff_eq_zero_of_degree_lt (lt_of_le_of_ne (le_of_not_gt h') h)]

/--
theorem `integralNormalization_mul_C_leadingCoeff` / 定理 `integralNormalization_mul_C_leadingCoeff`

English:
theorem integralNormalization_mul_C_leadingCoeff
  given: (p : R[X])
  proof: by
  ext i
  rw [coeff_mul_C]; rw [integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff]
  · simp only [coeff_scaleRoots]
    by_cases h' : i < p.degree
    · rw [mul_assoc, ← pow_succ, tsub_right_comm, tsub_add_cancel_of_le]
      rw [le_tsub_iff_

中文:
定理 integralNormalization_mul_C_leadingCoeff
  条件: (p : R[X])
  证明: by
  ext i
  rw [coeff_mul_C]; rw [integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff]
  · simp only [coeff_scaleRoots]
    by_cases h' : i < p.degree
    · rw [mul_assoc, ← pow_succ, tsub_right_comm, tsub_add_cancel_of_le]
      rw [le_tsub_iff_

Depends on / 依赖: Nat.succ_le_iff, coe_lt_degree, coe_lt_degree.mp, coeff_eq_zero_of_degree_lt, coeff_mul_C, coeff_scaleRoots, degree, integralNormalization_coeff, le_of_not_gt, le_tsub_iff_left, leadingCoeff, lt_of_le_of_ne, mul_assoc, natDegree_eq_of_degree_eq_some, p.degree, pow_succ, split_ifs, succ_le_iff, tsub_add_cancel_of_le, tsub_right_comm
-/
theorem integralNormalization_mul_C_leadingCoeff (p : R[X]) :
    integralNormalization p * C p.leadingCoeff = scaleRoots p p.leadingCoeff := by
  ext i
  rw [coeff_mul_C]; rw [integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff]
  · simp only [coeff_scaleRoots]
    by_cases h' : i < p.degree
    · rw [mul_assoc, ← pow_succ, tsub_right_comm, tsub_add_cancel_of_le]
      rw [le_tsub_iff_left (coe_lt_degree.mp h').le]; rw [Nat.succ_le_iff]
      exact coe_lt_degree.mp h'
    · simp [coeff_eq_zero_of_degree_lt (lt_of_le_of_ne (le_of_not_gt h') h)]

variable {A : Type*} [CommSemiring S] [Semiring A]

/--
theorem `leadingCoeff_smul_integralNormalization` / 定理 `leadingCoeff_smul_integralNormalization`

English:
theorem leadingCoeff_smul_integralNormalization
  given: (p : S[X])
  proof: by
  rw [Algebra.smul_def]; rw [algebraMap_eq]; rw [mul_comm]; rw [integralNormalization_mul_C_leadingCoeff]

中文:
定理 leadingCoeff_smul_integralNormalization
  条件: (p : S[X])
  证明: by
  rw [Algebra.smul_def]; rw [algebraMap_eq]; rw [mul_comm]; rw [integralNormalization_mul_C_leadingCoeff]

Depends on / 依赖: Algebra, Algebra.smul_def, algebraMap_eq, integralNormalization_mul_C_leadingCoeff, mul_comm, smul_def
-/
theorem leadingCoeff_smul_integralNormalization (p : S[X]) :
    p.leadingCoeff • integralNormalization p = scaleRoots p p.leadingCoeff := by
  rw [Algebra.smul_def]; rw [algebraMap_eq]; rw [mul_comm]; rw [integralNormalization_mul_C_leadingCoeff]

/--
theorem `integralNormalization_eval₂_leadingCoeff_mul_of_commute` / 定理 `integralNormalization_eval₂_leadingCoeff_mul_of_commute`

English:
theorem integralNormalization_eval₂_leadingCoeff_mul_of_commute
  statement: (h : 1 <= p.natDegree) (f : R ->+* A)
  proof: by
  rw [eval₂_eq_sum_range]; rw [eval₂_eq_sum_range]; rw [Finset.mul_sum]
  apply Finset.sum_congr
  · rw [natDegree_eq_of_degree_eq p.degree_integralNormalization]
  intro n _hn
  rw [h₁.mul_pow]; rw [← mul_assoc]; rw [← f.map_pow]; rw [← f.map_mul]; rw [integralNormalization_coeff_mul_leadingCoef

中文:
定理 integralNormalization_eval₂_leadingCoeff_mul_of_commute
  结论: (h : 1 <= p.natDegree) (f : R ->+* A)
  证明: by
  rw [eval₂_eq_sum_range]; rw [eval₂_eq_sum_range]; rw [Finset.mul_sum]
  apply Finset.sum_congr
  · rw [natDegree_eq_of_degree_eq p.degree_integralNormalization]
  intro n _hn
  rw [h₁.mul_pow]; rw [← mul_assoc]; rw [← f.map_pow]; rw [← f.map_mul]; rw [integralNormalization_coeff_mul_leadingCoef

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_congr, degree_integralNormalization, f.map_mul, f.map_pow, integralNormalization_coeff_mul_leadingCoeff_pow, map_mul, map_pow, mul_assoc, mul_pow, mul_sum, natDegree_eq_of_degree_eq, p.degree_integralNormalization, sum_congr
-/
theorem integralNormalization_eval₂_leadingCoeff_mul_of_commute (h : 1 <= p.natDegree) (f : R ->+* A)
    (x : A) (h₁ : Commute (f p.leadingCoeff) x) (h₂ : forall {r r'}, Commute (f r) (f r')) :
    (integralNormalization p).eval₂ f (f p.leadingCoeff * x) =
      f p.leadingCoeff ^ (p.natDegree - 1) * p.eval₂ f x := by
  rw [eval₂_eq_sum_range]; rw [eval₂_eq_sum_range]; rw [Finset.mul_sum]
  apply Finset.sum_congr
  · rw [natDegree_eq_of_degree_eq p.degree_integralNormalization]
  intro n _hn
  rw [h₁.mul_pow]; rw [← mul_assoc]; rw [← f.map_pow]; rw [← f.map_mul]; rw [integralNormalization_coeff_mul_leadingCoeff_pow _ h]; rw [f.map_mul]; rw [h₂.eq]; rw [f.map_pow]; rw [mul_assoc]

/--
theorem `integralNormalization_eval₂_leadingCoeff_mul` / 定理 `integralNormalization_eval₂_leadingCoeff_mul`

English:
theorem integralNormalization_eval₂_leadingCoeff_mul
  given: (h : 1 <= p.natDegree) (f : R ->+* S) (x : S)
  proof: integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ (.all _ _) (.all _ _)

中文:
定理 integralNormalization_eval₂_leadingCoeff_mul
  条件: (h : 1 <= p.natDegree) (f : R ->+* S) (x : S)
  证明: integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ (.all _ _) (.all _ _)
-/
theorem integralNormalization_eval₂_leadingCoeff_mul (h : 1 <= p.natDegree) (f : R ->+* S) (x : S) :
    (integralNormalization p).eval₂ f (f p.leadingCoeff * x) =
      f p.leadingCoeff ^ (p.natDegree - 1) * p.eval₂ f x :=
  integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ (.all _ _) (.all _ _)

/--
theorem `integralNormalization_eval₂_eq_zero_of_commute` / 定理 `integralNormalization_eval₂_eq_zero_of_commute`

English:
theorem integralNormalization_eval₂_eq_zero_of_commute
  statement: {p : R[X]} (f : R ->+* A) {z : A}
  proof: by
  obtain (h | h) := p.natDegree.eq_zero_or_pos
  · by_cases h0 : coeff p 0 = 0
    · rw [eq_C_of_natDegree_eq_zero h]
      simp [h0]
    · rw [eq_C_of_natDegree_eq_zero h, eval₂_C] at hz
      exact absurd (inj _ hz) h0
  · rw [integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ h₁ h₂,

中文:
定理 integralNormalization_eval₂_eq_zero_of_commute
  结论: {p : R[X]} (f : R ->+* A) {z : A}
  证明: by
  obtain (h | h) := p.natDegree.eq_zero_or_pos
  · by_cases h0 : coeff p 0 = 0
    · rw [eq_C_of_natDegree_eq_zero h]
      simp [h0]
    · rw [eq_C_of_natDegree_eq_zero h, eval₂_C] at hz
      exact absurd (inj _ hz) h0
  · rw [integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ h₁ h₂,

Depends on / 依赖: absurd, eq_C_of_natDegree_eq_zero, eq_zero_or_pos, mul_zero, natDegree, p.natDegree.eq_zero_or_pos
-/
theorem integralNormalization_eval₂_eq_zero_of_commute {p : R[X]} (f : R ->+* A) {z : A}
    (hz : eval₂ f z p = 0) (h₁ : Commute (f p.leadingCoeff) z) (h₂ : forall {r r'}, Commute (f r) (f r'))
    (inj : forall x : R, f x = 0 -> x = 0) :
    eval₂ f (f p.leadingCoeff * z) (integralNormalization p) = 0 := by
  obtain (h | h) := p.natDegree.eq_zero_or_pos
  · by_cases h0 : coeff p 0 = 0
    · rw [eq_C_of_natDegree_eq_zero h]
      simp [h0]
    · rw [eq_C_of_natDegree_eq_zero h, eval₂_C] at hz
      exact absurd (inj _ hz) h0
  · rw [integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ h₁ h₂, hz, mul_zero]

/--
theorem `integralNormalization_eval₂_eq_zero` / 定理 `integralNormalization_eval₂_eq_zero`

English:
theorem integralNormalization_eval₂_eq_zero
  statement: {p : R[X]} (f : R ->+* S) {z : S} (hz : eval₂ f z p = 0)
  proof: integralNormalization_eval₂_eq_zero_of_commute _ hz (.all _ _) (.all _ _) inj

中文:
定理 integralNormalization_eval₂_eq_zero
  结论: {p : R[X]} (f : R ->+* S) {z : S} (hz : eval₂ f z p = 0)
  证明: integralNormalization_eval₂_eq_zero_of_commute _ hz (.all _ _) (.all _ _) inj
-/
theorem integralNormalization_eval₂_eq_zero {p : R[X]} (f : R ->+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : forall x : R, f x = 0 -> x = 0) :
    eval₂ f (f p.leadingCoeff * z) (integralNormalization p) = 0 :=
  integralNormalization_eval₂_eq_zero_of_commute _ hz (.all _ _) (.all _ _) inj

/--
theorem `integralNormalization_aeval_eq_zero` / 定理 `integralNormalization_aeval_eq_zero`

English:
theorem integralNormalization_aeval_eq_zero
  statement: [Algebra S A] {f : S[X]} {z : A} (hz : aeval z f = 0)
  proof: integralNormalization_eval₂_eq_zero_of_commute (algebraMap S A) hz
    (Algebra.commute_algebraMap_left _ _) (.map (.all _ _) _) inj

中文:
定理 integralNormalization_aeval_eq_zero
  结论: [Algebra S A] {f : S[X]} {z : A} (hz : aeval z f = 0)
  证明: integralNormalization_eval₂_eq_zero_of_commute (algebraMap S A) hz
    (Algebra.commute_algebraMap_left _ _) (.map (.all _ _) _) inj

Depends on / 依赖: Algebra, Algebra.commute_algebraMap_left, ContinuousConstSMul, algebraMap, commute_algebraMap_left, continuousConstSMul, continuous_const_smul, continuous_dom, continuous_inclusion, isEmbedding_coe_of_principal, isEmbedding_coe_of_principal.continuousConstSMul
-/
theorem integralNormalization_aeval_eq_zero [Algebra S A] {f : S[X]} {z : A} (hz : aeval z f = 0)
    (inj : forall x : S, algebraMap S A x = 0 -> x = 0) :
    aeval (algebraMap S A f.leadingCoeff * z) (integralNormalization f) = 0 :=
  integralNormalization_eval₂_eq_zero_of_commute (algebraMap S A) hz
    (Algebra.commute_algebraMap_left _ _) (.map (.all _ _) _) inj

/--
lemma `integralNormalization_map` / 引理 `integralNormalization_map`

English:
lemma integralNormalization_map
  given: (f : R ->+* A) (p : R[X]) (H : f p.leadingCoeff != 0)
  proof: by
  ext i
  simp [integralNormalization_coeff, degree_map_eq_of_leadingCoeff_ne_zero _ H, apply_ite f,
    leadingCoeff_map_of_leadingCoeff_ne_zero _ H, natDegree_map_eq_iff.mpr (.inl H)]

中文:
引理 integralNormalization_map
  条件: (f : R ->+* A) (p : R[X]) (H : f p.leadingCoeff != 0)
  证明: by
  ext i
  simp [integralNormalization_coeff, degree_map_eq_of_leadingCoeff_ne_zero _ H, apply_ite f,
    leadingCoeff_map_of_leadingCoeff_ne_zero _ H, natDegree_map_eq_iff.mpr (.inl H)]

Depends on / 依赖: apply_ite, degree_map_eq_of_leadingCoeff_ne_zero, integralNormalization_coeff, leadingCoeff_map_of_leadingCoeff_ne_zero, natDegree_map_eq_iff, natDegree_map_eq_iff.mpr
-/
lemma integralNormalization_map (f : R ->+* A) (p : R[X]) (H : f p.leadingCoeff != 0) :
    (p.map f).integralNormalization = p.integralNormalization.map f := by
  ext i
  simp [integralNormalization_coeff, degree_map_eq_of_leadingCoeff_ne_zero _ H, apply_ite f,
    leadingCoeff_map_of_leadingCoeff_ne_zero _ H, natDegree_map_eq_iff.mpr (.inl H)]

end Semiring

section IsCancelMulZero

variable [Semiring R] [IsCancelMulZero R]

@[simp]
/--
theorem `support_integralNormalization` / 定理 `support_integralNormalization`

English:
theorem support_integralNormalization
  given: {f : R[X]}
  proof: by
  nontriviality R using Subsingleton.eq_zero (α := R[X])
  have : IsDomain R := {}
  by_cases hf : f = 0; · simp [hf]
  ext i
  refine ⟨fun h => support_integralNormalization_subset h, ?_⟩
  simp only [integralNormalization_coeff, mem_support_iff]
  intro hfi
  split_ifs with hi <;> simp [hf, hfi

中文:
定理 support_integralNormalization
  条件: {f : R[X]}
  证明: by
  nontriviality R using Subsingleton.eq_zero (α := R[X])
  have : IsDomain R := {}
  by_cases hf : f = 0; · simp [hf]
  ext i
  refine ⟨fun h => support_integralNormalization_subset h, ?_⟩
  simp only [integralNormalization_coeff, mem_support_iff]
  intro hfi
  split_ifs with hi <;> simp [hf, hfi

Depends on / 依赖: IsDomain, Subsingleton, Subsingleton.eq_zero, continuousSMul, continuous_id, eq_zero, integralNormalization_coeff, isEmbedding_coe_of_principal, isEmbedding_coe_of_principal.continuousSMul, mem_support_iff, nontriviality, split_ifs, support_integralNormalization_subset
-/
theorem support_integralNormalization {f : R[X]} :
    (integralNormalization f).support = f.support := by
  nontriviality R using Subsingleton.eq_zero (α := R[X])
  have : IsDomain R := {}
  by_cases hf : f = 0; · simp [hf]
  ext i
  refine ⟨fun h => support_integralNormalization_subset h, ?_⟩
  simp only [integralNormalization_coeff, mem_support_iff]
  intro hfi
  split_ifs with hi <;> simp [hf, hfi]

end IsCancelMulZero

end IntegralNormalization

end Polynomial
