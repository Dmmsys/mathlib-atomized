/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Regular.SMul

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`Monic.mul`, `Monic.map`, `Monic.pow`.
-/

@[expose] public section


noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : Nat} {ι : Type y}

section Semiring

variable [Semiring R] {p q r : R[X]}

/--
theorem `monic_zero_iff_subsingleton` / 定理 `monic_zero_iff_subsingleton`

English:
theorem monic_zero_iff_subsingleton
  statement: Monic (0 : R[X]) ↔ Subsingleton R
  proof: subsingleton_iff_zero_eq_one

中文:
定理 monic_zero_iff_subsingleton
  结论: Monic (0 : R[X]) ↔ 子单例 R
  证明: subsingleton_iff_zero_eq_one

Depends on / 依赖: subsingleton_iff_zero_eq_one
-/
theorem monic_zero_iff_subsingleton : Monic (0 : R[X]) ↔ Subsingleton R :=
  subsingleton_iff_zero_eq_one

/--
theorem `not_monic_zero_iff` / 定理 `not_monic_zero_iff`

English:
theorem not_monic_zero_iff
  statement: ¬Monic (0 : R[X]) ↔ (0 : R) != 1
  proof: (monic_zero_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm).not

中文:
定理 not_monic_zero_iff
  结论: ¬Monic (0 : R[X]) ↔ (0 : R) != 1
  证明: (monic_zero_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm).not

Depends on / 依赖: monic_zero_iff_subsingleton, monic_zero_iff_subsingleton.trans, subsingleton_iff_zero_eq_one, subsingleton_iff_zero_eq_one.symm
-/
theorem not_monic_zero_iff : ¬Monic (0 : R[X]) ↔ (0 : R) != 1 :=
  (monic_zero_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm).not

/--
theorem `monic_zero_iff_subsingleton'` / 定理 `monic_zero_iff_subsingleton'`

English:
theorem monic_zero_iff_subsingleton'
  proof: Polynomial.monic_zero_iff_subsingleton.trans
    ⟨by
      intro
      simp [eq_iff_true_of_subsingleton], fun h => subsingleton_iff.mpr h.2⟩

中文:
定理 monic_zero_iff_subsingleton'
  证明: Polynomial.monic_zero_iff_subsingleton.trans
    ⟨by
      intro
      simp [eq_iff_true_of_subsingleton], fun h => subsingleton_iff.mpr h.2⟩

Depends on / 依赖: Polynomial, Polynomial.monic_zero_iff_subsingleton.trans, eq_iff_true_of_subsingleton, monic_zero_iff_subsingleton, subsingleton_iff, subsingleton_iff.mpr
-/
theorem monic_zero_iff_subsingleton' :
    Monic (0 : R[X]) ↔ (forall f g : R[X], f = g) ∧ forall a b : R, a = b :=
  Polynomial.monic_zero_iff_subsingleton.trans
    ⟨by
      intro
      simp [eq_iff_true_of_subsingleton], fun h => subsingleton_iff.mpr h.2⟩

/--
theorem `Monic.as_sum` / 定理 `Monic.as_sum`

English:
theorem Monic.as_sum
  given: (hp : p.Monic)
  proof: by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm]
  suffices C (p.coeff p.natDegree) = 1 by rw [this, one_mul]
  exact congr_arg C hp

中文:
定理 Monic.as_sum
  条件: (hp : p.Monic)
  证明: by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm]
  suffices C (p.coeff p.natDegree) = 1 by rw [this, one_mul]
  exact congr_arg C hp

Depends on / 依赖: as_sum_range_C_mul_X_pow, congr_arg, conv_lhs, natDegree, one_mul, p.as_sum_range_C_mul_X_pow, p.coeff, p.natDegree, sum_range_succ_comm
-/
theorem Monic.as_sum (hp : p.Monic) :
    p = X ^ p.natDegree + ∑ i in range p.natDegree, C (p.coeff i) * X ^ i := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm]
  suffices C (p.coeff p.natDegree) = 1 by rw [this, one_mul]
  exact congr_arg C hp

/--
theorem `Monic.map` / 定理 `Monic.map`

English:
theorem Monic.map
  given: [Semiring S] (f : R ->+* S) (hp : Monic p)
  statement: Monic (p.map f)
  proof: .elim (·.elim ..) fun _ => subsingleton_or_nontrivial S
f.map_one ▸ hp ▸ leadingCoeff_map_eq_of_isUnit_leadingCoeff _ isUnit_one

中文:
定理 Monic.map
  条件: [半环 S] (f : R ->+* S) (hp : Monic p)
  结论: Monic (p.map f)
  证明: .elim (·.elim ..) fun _ => subsingleton_or_nontrivial S
f.map_one ▸ hp ▸ leadingCoeff_map_eq_of_isUnit_leadingCoeff _ isUnit_one

Depends on / 依赖: f.map_one, isUnit_one, leadingCoeff_map_eq_of_isUnit_leadingCoeff, map_one, subsingleton_or_nontrivial
-/
theorem Monic.map [Semiring S] (f : R ->+* S) (hp : Monic p) : Monic (p.map f) :=
.elim (·.elim ..) fun _ => subsingleton_or_nontrivial S
f.map_one ▸ hp ▸ leadingCoeff_map_eq_of_isUnit_leadingCoeff _ isUnit_one

/--
theorem `monic_C_mul_of_mul_leadingCoeff_eq_one` / 定理 `monic_C_mul_of_mul_leadingCoeff_eq_one`

English:
theorem monic_C_mul_of_mul_leadingCoeff_eq_one
  given: {b : R} (hp : b * p.leadingCoeff = 1)
  proof: by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

中文:
定理 monic_C_mul_of_mul_leadingCoeff_eq_one
  条件: {b : R} (hp : b * p.leadingCoeff = 1)
  证明: by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

Depends on / 依赖: leadingCoeff_C, leadingCoeff_mul, nontriviality
-/
theorem monic_C_mul_of_mul_leadingCoeff_eq_one {b : R} (hp : b * p.leadingCoeff = 1) :
    Monic (C b * p) := by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

/--
theorem `monic_mul_C_of_leadingCoeff_mul_eq_one` / 定理 `monic_mul_C_of_leadingCoeff_mul_eq_one`

English:
theorem monic_mul_C_of_leadingCoeff_mul_eq_one
  given: {b : R} (hp : p.leadingCoeff * b = 1)
  proof: by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

中文:
定理 monic_mul_C_of_leadingCoeff_mul_eq_one
  条件: {b : R} (hp : p.leadingCoeff * b = 1)
  证明: by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

Depends on / 依赖: leadingCoeff_C, leadingCoeff_mul, nontriviality
-/
theorem monic_mul_C_of_leadingCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) :
    Monic (p * C b) := by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

/--
theorem `monic_X_pow_add` / 定理 `monic_X_pow_add`

English:
theorem monic_X_pow_add
  given: {n : Nat} (H : degree p < n)
  statement: Monic (X ^ n + p)
  proof: monic_of_degree_le n
    (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H)))
    (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H, add_zero])

中文:
定理 monic_X_pow_add
  条件: {n : 自然数} (H : degree p < n)
  结论: Monic (X ^ n + p)
  证明: monic_of_degree_le n
    (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H)))
    (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H, add_zero])

Depends on / 依赖: add_zero, coeff_X_pow, coeff_add, coeff_eq_zero_of_degree_lt, degree_X_pow_le, degree_add_le, if_pos, le_of_lt, le_trans, max_le, monic_of_degree_le
-/
theorem monic_X_pow_add {n : Nat} (H : degree p < n) : Monic (X ^ n + p) :=
  monic_of_degree_le n
    (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H)))
    (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H, add_zero])

variable (a) in
/--
theorem `monic_X_pow_add_C` / 定理 `monic_X_pow_add_C`

English:
theorem monic_X_pow_add_C
  given: {n : Nat} (h : n != 0)
  statement: (X ^ n + C a).Monic
  proof: monic_X_pow_add (lt_of_le_of_lt degree_C_le
    (by simp only [Nat.cast_pos, Nat.pos_iff_ne_zero, ne_eq, h, not_false_eq_true]))

中文:
定理 monic_X_pow_add_C
  条件: {n : 自然数} (h : n != 0)
  结论: (X ^ n + C a).Monic
  证明: monic_X_pow_add (lt_of_le_of_lt degree_C_le
    (by simp only [Nat.cast_pos, Nat.pos_iff_ne_zero, ne_eq, h, not_false_eq_true]))

Depends on / 依赖: Nat.cast_pos, Nat.pos_iff_ne_zero, cast_pos, degree_C_le, lt_of_le_of_lt, monic_X_pow_add, ne_eq, not_false_eq_true, pos_iff_ne_zero
-/
theorem monic_X_pow_add_C {n : Nat} (h : n != 0) : (X ^ n + C a).Monic :=
monic_X_pow_add (lt_of_le_of_lt degree_C_le
    (by simp only [Nat.cast_pos, Nat.pos_iff_ne_zero, ne_eq, h, not_false_eq_true]))

/--
theorem `monic_X_add_C` / 定理 `monic_X_add_C`

English:
theorem monic_X_add_C
  given: (x : R)
  statement: Monic (X + C x)
  proof: pow_one (X : R[X]) ▸ monic_X_pow_add_C x one_ne_zero

中文:
定理 monic_X_add_C
  条件: (x : R)
  结论: Monic (X + C x)
  证明: pow_one (X : R[X]) ▸ monic_X_pow_add_C x one_ne_zero

Depends on / 依赖: monic_X_pow_add_C, one_ne_zero, pow_one
-/
theorem monic_X_add_C (x : R) : Monic (X + C x) :=
  pow_one (X : R[X]) ▸ monic_X_pow_add_C x one_ne_zero

/--
theorem `Monic.mul` / 定理 `Monic.mul`

English:
theorem Monic.mul
  given: (hp : Monic p) (hq : Monic q)
  statement: Monic (p * q)
  proof: letI := Classical.decEq R
  if h0 : (0 : R) = 1 then
    haveI := subsingleton_of_zero_eq_one h0
    Subsingleton.elim _ _
  else by
    have : p.leadingCoeff * q.leadingCoeff != 0 := by
      simp [Monic.def.1 hp, Monic.def.1 hq, Ne.symm h0]
    rw [Monic.def]; rw [leadingCoeff_mul' this]; rw [Monic.def.1 hp]; rw [Monic.def.1 hq]; rw [one_mul]

中文:
定理 Monic.mul
  条件: (hp : Monic p) (hq : Monic q)
  结论: Monic (p * q)
  证明: letI := Classical.decEq R
  if h0 : (0 : R) = 1 then
    haveI := subsingleton_of_zero_eq_one h0
    Subsingleton.elim _ _
  else by
    have : p.leadingCoeff * q.leadingCoeff != 0 := by
      simp [Monic.def.1 hp, Monic.def.1 hq, Ne.symm h0]
    rw [Monic.def]; rw [leadingCoeff_mul' this]; rw [Monic.def.1 hp]; rw [Monic.def.1 hq]; rw [one_mul]
-/
theorem Monic.mul (hp : Monic p) (hq : Monic q) : Monic (p * q) :=
  letI := Classical.decEq R
  if h0 : (0 : R) = 1 then
    haveI := subsingleton_of_zero_eq_one h0
    Subsingleton.elim _ _
  else by
    have : p.leadingCoeff * q.leadingCoeff != 0 := by
      simp [Monic.def.1 hp, Monic.def.1 hq, Ne.symm h0]
    rw [Monic.def]; rw [leadingCoeff_mul' this]; rw [Monic.def.1 hp]; rw [Monic.def.1 hq]; rw [one_mul]

/--
theorem `Monic.pow` / 定理 `Monic.pow`

English:
theorem Monic.pow
  given: (hp : Monic p)
  statement: forall n : Nat, Monic (p ^ n)

中文:
定理 Monic.pow
  条件: (hp : Monic p)
  结论: 对任意 n : 自然数, Monic (p ^ n)
-/
theorem Monic.pow (hp : Monic p) : forall n : Nat, Monic (p ^ n)
  | 0 => monic_one
  | n + 1 => by
    rw [pow_succ]
    exact (Monic.pow hp n).mul hp

/--
theorem `Monic.add_of_left` / 定理 `Monic.add_of_left`

English:
theorem Monic.add_of_left
  given: (hp : Monic p) (hpq : degree q < degree p)
  statement: Monic (p + q)
  proof: by
  rwa [Monic, add_comm, leadingCoeff_add_of_degree_lt hpq]

中文:
定理 Monic.add_of_left
  条件: (hp : Monic p) (hpq : degree q < degree p)
  结论: Monic (p + q)
  证明: by
  rwa [Monic, add_comm, leadingCoeff_add_of_degree_lt hpq]

Depends on / 依赖: add_comm, leadingCoeff_add_of_degree_lt
-/
theorem Monic.add_of_left (hp : Monic p) (hpq : degree q < degree p) : Monic (p + q) := by
  rwa [Monic, add_comm, leadingCoeff_add_of_degree_lt hpq]

/--
theorem `Monic.add_of_right` / 定理 `Monic.add_of_right`

English:
theorem Monic.add_of_right
  given: (hq : Monic q) (hpq : degree p < degree q)
  statement: Monic (p + q)
  proof: by
  rwa [Monic, leadingCoeff_add_of_degree_lt hpq]

中文:
定理 Monic.add_of_right
  条件: (hq : Monic q) (hpq : degree p < degree q)
  结论: Monic (p + q)
  证明: by
  rwa [Monic, leadingCoeff_add_of_degree_lt hpq]

Depends on / 依赖: leadingCoeff_add_of_degree_lt
-/
theorem Monic.add_of_right (hq : Monic q) (hpq : degree p < degree q) : Monic (p + q) := by
  rwa [Monic, leadingCoeff_add_of_degree_lt hpq]

/--
theorem `Monic.of_mul_monic_left` / 定理 `Monic.of_mul_monic_left`

English:
theorem Monic.of_mul_monic_left
  given: (hp : p.Monic) (hpq : (p * q).Monic)
  statement: q.Monic
  proof: by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_monic_mul hp]

中文:
定理 Monic.of_mul_monic_left
  条件: (hp : p.Monic) (hpq : (p * q).Monic)
  结论: q.Monic
  证明: by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_monic_mul hp]

Depends on / 依赖: Monic.def, contrapose, leadingCoeff_monic_mul
-/
theorem Monic.of_mul_monic_left (hp : p.Monic) (hpq : (p * q).Monic) : q.Monic := by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_monic_mul hp]

/--
theorem `Monic.of_mul_monic_right` / 定理 `Monic.of_mul_monic_right`

English:
theorem Monic.of_mul_monic_right
  given: (hq : q.Monic) (hpq : (p * q).Monic)
  statement: p.Monic
  proof: by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_mul_monic hq]

中文:
定理 Monic.of_mul_monic_right
  条件: (hq : q.Monic) (hpq : (p * q).Monic)
  结论: p.Monic
  证明: by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_mul_monic hq]

Depends on / 依赖: Monic.def, contrapose, leadingCoeff_mul_monic
-/
theorem Monic.of_mul_monic_right (hq : q.Monic) (hpq : (p * q).Monic) : p.Monic := by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_mul_monic hq]

namespace Monic

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: (hp : p.Monic) (hq : q.Monic) (h : q.natDegree != 0)
  statement: (p.comp q).Monic
  proof: by
  nontriviality R
  have : (p.comp q).natDegree = p.natDegree * q.natDegree :=
natDegree_comp_eq_of_mul_ne_zero by simp [hp.leadingCoeff, hq.leadingCoeff]
  rw [Monic.def]; rw [Polynomial.leadingCoeff]; rw [this]; rw [coeff_comp_degree_mul_degree h]; rw [hp.leadingCoeff]; rw [hq.leadingCoeff]; rw [one_pow]; rw [mul_one]

中文:
引理 comp
  条件: (hp : p.Monic) (hq : q.Monic) (h : q.natDegree != 0)
  结论: (p.comp q).Monic
  证明: by
  nontriviality R
  have : (p.comp q).natDegree = p.natDegree * q.natDegree :=
natDegree_comp_eq_of_mul_ne_zero by simp [hp.leadingCoeff, hq.leadingCoeff]
  rw [Monic.def]; rw [Polynomial.leadingCoeff]; rw [this]; rw [coeff_comp_degree_mul_degree h]; rw [hp.leadingCoeff]; rw [hq.leadingCoeff]; rw [one_pow]; rw [mul_one]

Depends on / 依赖: Monic.def, Polynomial, Polynomial.leadingCoeff, coeff_comp_degree_mul_degree, hp.leadingCoeff, hq.leadingCoeff, leadingCoeff, mul_one, natDegree, natDegree_comp_eq_of_mul_ne_zero, nontriviality, one_pow, p.comp, p.natDegree, q.natDegree
-/
lemma comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree != 0) : (p.comp q).Monic := by
  nontriviality R
  have : (p.comp q).natDegree = p.natDegree * q.natDegree :=
natDegree_comp_eq_of_mul_ne_zero by simp [hp.leadingCoeff, hq.leadingCoeff]
  rw [Monic.def]; rw [Polynomial.leadingCoeff]; rw [this]; rw [coeff_comp_degree_mul_degree h]; rw [hp.leadingCoeff]; rw [hq.leadingCoeff]; rw [one_pow]; rw [mul_one]

/--
lemma `comp_X_add_C` / 引理 `comp_X_add_C`

English:
lemma comp_X_add_C
  given: (hp : p.Monic) (r : R)
  statement: (p.comp (X + C r)).Monic
  proof: by
  nontriviality R
  refine hp.comp (monic_X_add_C _) fun ha => ?_
  rw [natDegree_X_add_C] at ha
  exact one_ne_zero ha

@[simp]

中文:
引理 comp_X_add_C
  条件: (hp : p.Monic) (r : R)
  结论: (p.comp (X + C r)).Monic
  证明: by
  nontriviality R
  refine hp.comp (monic_X_add_C _) fun ha => ?_
  rw [natDegree_X_add_C] at ha
  exact one_ne_zero ha

@[simp]

Depends on / 依赖: hp.comp, monic_X_add_C, natDegree_X_add_C, nontriviality, one_ne_zero
-/
lemma comp_X_add_C (hp : p.Monic) (r : R) : (p.comp (X + C r)).Monic := by
  nontriviality R
  refine hp.comp (monic_X_add_C _) fun ha => ?_
  rw [natDegree_X_add_C] at ha
  exact one_ne_zero ha

@[simp]
/--
theorem `degree_le_zero_iff_eq_one` / 定理 `degree_le_zero_iff_eq_one`

English:
theorem degree_le_zero_iff_eq_one
  given: (hp : p.Monic)
  statement: p.degree <= 0 ↔ p = 1
  proof: by
  rw [← hp.natDegree_eq_zero]; rw [natDegree_eq_zero_iff_degree_le_zero]

中文:
定理 degree_le_zero_iff_eq_one
  条件: (hp : p.Monic)
  结论: p.degree <= 0 ↔ p = 1
  证明: by
  rw [← hp.natDegree_eq_zero]; rw [natDegree_eq_zero_iff_degree_le_zero]

Depends on / 依赖: hp.natDegree_eq_zero, natDegree_eq_zero, natDegree_eq_zero_iff_degree_le_zero
-/
theorem degree_le_zero_iff_eq_one (hp : p.Monic) : p.degree <= 0 ↔ p = 1 := by
  rw [← hp.natDegree_eq_zero]; rw [natDegree_eq_zero_iff_degree_le_zero]

/--
theorem `natDegree_mul` / 定理 `natDegree_mul`

English:
theorem natDegree_mul
  given: (hp : p.Monic) (hq : q.Monic)
  proof: by
  nontriviality R
  apply natDegree_mul'
  simp [hp.leadingCoeff, hq.leadingCoeff]

中文:
定理 natDegree_mul
  条件: (hp : p.Monic) (hq : q.Monic)
  证明: by
  nontriviality R
  apply natDegree_mul'
  simp [hp.leadingCoeff, hq.leadingCoeff]

Depends on / 依赖: hp.leadingCoeff, hq.leadingCoeff, leadingCoeff, natDegree_mul, nontriviality
-/
theorem natDegree_mul (hp : p.Monic) (hq : q.Monic) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  nontriviality R
  apply natDegree_mul'
  simp [hp.leadingCoeff, hq.leadingCoeff]

/--
theorem `degree_mul_comm` / 定理 `degree_mul_comm`

English:
theorem degree_mul_comm
  given: (hp : p.Monic) (q : R[X])
  statement: (p * q).degree = (q * p).degree
  proof: by
  by_cases h : q = 0
  · simp [h]
  rw [degree_mul']; rw [hp.degree_mul]
  · exact add_comm _ _
  · rwa [hp.leadingCoeff, one_mul, leadingCoeff_ne_zero]

nonrec theorem natDegree_mul' (hp : p.Monic) (hq : q != 0) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  rw [natDegree_mul']
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

中文:
定理 degree_mul_comm
  条件: (hp : p.Monic) (q : R[X])
  结论: (p * q).degree = (q * p).degree
  证明: by
  by_cases h : q = 0
  · simp [h]
  rw [degree_mul']; rw [hp.degree_mul]
  · exact add_comm _ _
  · rwa [hp.leadingCoeff, one_mul, leadingCoeff_ne_zero]

nonrec theorem natDegree_mul' (hp : p.Monic) (hq : q != 0) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  rw [natDegree_mul']
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

Depends on / 依赖: add_comm, degree_mul, hp.degree_mul, hp.leadingCoeff, leadingCoeff, leadingCoeff_ne_zero, one_mul
-/
theorem degree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).degree = (q * p).degree := by
  by_cases h : q = 0
  · simp [h]
  rw [degree_mul']; rw [hp.degree_mul]
  · exact add_comm _ _
  · rwa [hp.leadingCoeff, one_mul, leadingCoeff_ne_zero]

nonrec theorem natDegree_mul' (hp : p.Monic) (hq : q != 0) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  rw [natDegree_mul']
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

/--
theorem `natDegree_mul_comm` / 定理 `natDegree_mul_comm`

English:
theorem natDegree_mul_comm
  given: (hp : p.Monic) (q : R[X])
  statement: (p * q).natDegree = (q * p).natDegree
  proof: by
  by_cases h : q = 0
  · simp [h]
  rw [hp.natDegree_mul' h]; rw [Polynomial.natDegree_mul']; rw [add_comm]
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

中文:
定理 natDegree_mul_comm
  条件: (hp : p.Monic) (q : R[X])
  结论: (p * q).natDegree = (q * p).natDegree
  证明: by
  by_cases h : q = 0
  · simp [h]
  rw [hp.natDegree_mul' h]; rw [Polynomial.natDegree_mul']; rw [add_comm]
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

Depends on / 依赖: Polynomial, Polynomial.natDegree_mul, add_comm, hp.leadingCoeff, hp.natDegree_mul, leadingCoeff, leadingCoeff_ne_zero, natDegree_mul
-/
theorem natDegree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).natDegree = (q * p).natDegree := by
  by_cases h : q = 0
  · simp [h]
  rw [hp.natDegree_mul' h]; rw [Polynomial.natDegree_mul']; rw [add_comm]
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

/--
theorem `_root_.Polynomial.not_isUnit_X_add_C` / 定理 `_root_.Polynomial.not_isUnit_X_add_C`

English:
theorem _root_.Polynomial.not_isUnit_X_add_C
  given: [Nontrivial R] (a : R)
  statement: ¬ IsUnit (X + C a)
  proof: by
  rintro ⟨⟨_, g, hfg, hgf⟩, rfl⟩
  have h := (monic_X_add_C a).natDegree_mul' (right_ne_zero_of_mul_eq_one hfg)
  rw [hfg]; rw [natDegree_one]; rw [natDegree_X_add_C] at h
  grind

中文:
定理 _root_.多项式.not_isUnit_X_add_C
  条件: [非平凡 R] (a : R)
  结论: ¬ 是单位 (X + C a)
  证明: by
  rintro ⟨⟨_, g, hfg, hgf⟩, rfl⟩
  have h := (monic_X_add_C a).natDegree_mul' (right_ne_zero_of_mul_eq_one hfg)
  rw [hfg]; rw [natDegree_one]; rw [natDegree_X_add_C] at h
  grind

Depends on / 依赖: monic_X_add_C, natDegree_X_add_C, natDegree_mul, natDegree_one, right_ne_zero_of_mul_eq_one
-/
theorem _root_.Polynomial.not_isUnit_X_add_C [Nontrivial R] (a : R) : ¬ IsUnit (X + C a) := by
  rintro ⟨⟨_, g, hfg, hgf⟩, rfl⟩
  have h := (monic_X_add_C a).natDegree_mul' (right_ne_zero_of_mul_eq_one hfg)
  rw [hfg]; rw [natDegree_one]; rw [natDegree_X_add_C] at h
  grind

/--
theorem `not_dvd_of_natDegree_lt` / 定理 `not_dvd_of_natDegree_lt`

English:
theorem not_dvd_of_natDegree_lt
  given: (hp : Monic p) (h0 : q != 0) (hl : natDegree q < natDegree p)
  proof: by
  rintro ⟨r, rfl⟩
  rw [hp.natDegree_mul' <| right_ne_zero_of_mul h0] at hl
  exact hl.not_ge (Nat.le_add_right _ _)

中文:
定理 not_dvd_of_natDegree_lt
  条件: (hp : Monic p) (h0 : q != 0) (hl : natDegree q < natDegree p)
  证明: by
  rintro ⟨r, rfl⟩
  rw [hp.natDegree_mul' <| right_ne_zero_of_mul h0] at hl
  exact hl.not_ge (Nat.le_add_right _ _)

Depends on / 依赖: Nat.le_add_right, hl.not_ge, hp.natDegree_mul, le_add_right, natDegree_mul, not_ge, right_ne_zero_of_mul
-/
theorem not_dvd_of_natDegree_lt (hp : Monic p) (h0 : q != 0) (hl : natDegree q < natDegree p) :
    ¬p ∣ q := by
  rintro ⟨r, rfl⟩
  rw [hp.natDegree_mul' <| right_ne_zero_of_mul h0] at hl
  exact hl.not_ge (Nat.le_add_right _ _)

/--
theorem `not_dvd_of_degree_lt` / 定理 `not_dvd_of_degree_lt`

English:
theorem not_dvd_of_degree_lt
  given: (hp : Monic p) (h0 : q != 0) (hl : degree q < degree p)
  statement: ¬p ∣ q
  proof: Monic.not_dvd_of_natDegree_lt hp h0 natDegree_lt_natDegree h0 hl

中文:
定理 not_dvd_of_degree_lt
  条件: (hp : Monic p) (h0 : q != 0) (hl : degree q < degree p)
  结论: ¬p ∣ q
  证明: Monic.not_dvd_of_natDegree_lt hp h0 natDegree_lt_natDegree h0 hl

Depends on / 依赖: Monic.not_dvd_of_natDegree_lt, natDegree_lt_natDegree, not_dvd_of_natDegree_lt
-/
theorem not_dvd_of_degree_lt (hp : Monic p) (h0 : q != 0) (hl : degree q < degree p) : ¬p ∣ q :=
Monic.not_dvd_of_natDegree_lt hp h0 natDegree_lt_natDegree h0 hl

/--
theorem `nextCoeff_mul` / 定理 `nextCoeff_mul`

English:
theorem nextCoeff_mul
  given: (hp : Monic p) (hq : Monic q)
  proof: by
  nontriviality
  simp only [← coeff_one_reverse]
  rw [reverse_mul] <;> simp [hp.leadingCoeff, hq.leadingCoeff, mul_coeff_one, add_comm]

中文:
定理 nextCoeff_mul
  条件: (hp : Monic p) (hq : Monic q)
  证明: by
  nontriviality
  simp only [← coeff_one_reverse]
  rw [reverse_mul] <;> simp [hp.leadingCoeff, hq.leadingCoeff, mul_coeff_one, add_comm]

Depends on / 依赖: add_comm, coeff_one_reverse, hp.leadingCoeff, hq.leadingCoeff, leadingCoeff, mul_coeff_one, nontriviality, reverse_mul
-/
theorem nextCoeff_mul (hp : Monic p) (hq : Monic q) :
    nextCoeff (p * q) = nextCoeff p + nextCoeff q := by
  nontriviality
  simp only [← coeff_one_reverse]
  rw [reverse_mul] <;> simp [hp.leadingCoeff, hq.leadingCoeff, mul_coeff_one, add_comm]

/--
theorem `nextCoeff_pow` / 定理 `nextCoeff_pow`

English:
theorem nextCoeff_pow
  given: (hp : p.Monic) (n : Nat)
  statement: (p ^ n).nextCoeff = n • p.nextCoeff
  proof: by
  induction n with
  | zero => rw [pow_zero, zero_smul, ← map_one (f := C), nextCoeff_C_eq_zero]
  | succ n ih => rw [pow_succ, (hp.pow n).nextCoeff_mul hp, ih, succ_nsmul]

中文:
定理 nextCoeff_pow
  条件: (hp : p.Monic) (n : 自然数)
  结论: (p ^ n).nextCoeff = n • p.nextCoeff
  证明: by
  induction n with
  | zero => rw [pow_zero, zero_smul, ← map_one (f := C), nextCoeff_C_eq_zero]
  | succ n ih => rw [pow_succ, (hp.pow n).nextCoeff_mul hp, ih, succ_nsmul]

Depends on / 依赖: hp.pow, map_one, nextCoeff_C_eq_zero, nextCoeff_mul, pow_succ, pow_zero, succ_nsmul, zero_smul
-/
theorem nextCoeff_pow (hp : p.Monic) (n : Nat) : (p ^ n).nextCoeff = n • p.nextCoeff := by
  induction n with
  | zero => rw [pow_zero, zero_smul, ← map_one (f := C), nextCoeff_C_eq_zero]
  | succ n ih => rw [pow_succ, (hp.pow n).nextCoeff_mul hp, ih, succ_nsmul]

/--
theorem `eq_one_of_map_eq_one` / 定理 `eq_one_of_map_eq_one`

English:
theorem eq_one_of_map_eq_one
  statement: {S : Type*} [Semiring S] [Nontrivial S] (f : R ->+* S) (hp : p.Monic)
  proof: by
  nontriviality R
  have hdeg : p.degree = 0 := by
    rw [← degree_map_eq_of_leadingCoeff_ne_zero f _]; rw [map_eq]; rw [degree_one]
    · rw [hp.leadingCoeff, f.map_one]
      exact one_ne_zero
  have hndeg : p.natDegree = 0 :=
    WithBot.coe_eq_coe.mp ((degree_eq_natDegree hp.ne_zero).symm.trans hdeg)
  convert! eq_C_of_degree_eq_zero hdeg
  rw [← hndeg]; rw [← Polynomial.leadingCoeff]; rw [hp.leadingCoeff]; rw [C.map_one]

中文:
定理 eq_one_of_map_eq_one
  结论: {S : 类型} [半环 S] [非平凡 S] (f : R ->+* S) (hp : p.Monic)
  证明: by
  nontriviality R
  have hdeg : p.degree = 0 := by
    rw [← degree_map_eq_of_leadingCoeff_ne_zero f _]; rw [map_eq]; rw [degree_one]
    · rw [hp.leadingCoeff, f.map_one]
      exact one_ne_zero
  have hndeg : p.natDegree = 0 :=
    WithBot.coe_eq_coe.mp ((degree_eq_natDegree hp.ne_zero).symm.trans hdeg)
  convert! eq_C_of_degree_eq_zero hdeg
  rw [← hndeg]; rw [← Polynomial.leadingCoeff]; rw [hp.leadingCoeff]; rw [C.map_one]

Depends on / 依赖: C.map_one, Polynomial, Polynomial.leadingCoeff, WithBot, WithBot.coe_eq_coe.mp, coe_eq_coe, convert, degree, degree_eq_natDegree, degree_map_eq_of_leadingCoeff_ne_zero, degree_one, eq_C_of_degree_eq_zero, f.map_one, hp.leadingCoeff, hp.ne_zero, leadingCoeff, map_eq, map_one, natDegree, ne_zero
-/
theorem eq_one_of_map_eq_one {S : Type*} [Semiring S] [Nontrivial S] (f : R ->+* S) (hp : p.Monic)
    (map_eq : p.map f = 1) : p = 1 := by
  nontriviality R
  have hdeg : p.degree = 0 := by
    rw [← degree_map_eq_of_leadingCoeff_ne_zero f _]; rw [map_eq]; rw [degree_one]
    · rw [hp.leadingCoeff, f.map_one]
      exact one_ne_zero
  have hndeg : p.natDegree = 0 :=
    WithBot.coe_eq_coe.mp ((degree_eq_natDegree hp.ne_zero).symm.trans hdeg)
  convert! eq_C_of_degree_eq_zero hdeg
  rw [← hndeg]; rw [← Polynomial.leadingCoeff]; rw [hp.leadingCoeff]; rw [C.map_one]

/--
theorem `natDegree_pow` / 定理 `natDegree_pow`

English:
theorem natDegree_pow
  given: (hp : p.Monic) (n : Nat)
  statement: (p ^ n).natDegree = n * p.natDegree
  proof: by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, (hp.pow n).natDegree_mul hp, hn, Nat.succ_mul, add_comm]

中文:
定理 natDegree_pow
  条件: (hp : p.Monic) (n : 自然数)
  结论: (p ^ n).natDegree = n * p.natDegree
  证明: by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, (hp.pow n).natDegree_mul hp, hn, Nat.succ_mul, add_comm]

Depends on / 依赖: Nat.succ_mul, add_comm, hp.pow, natDegree_mul, pow_succ, succ_mul
-/
theorem natDegree_pow (hp : p.Monic) (n : Nat) : (p ^ n).natDegree = n * p.natDegree := by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, (hp.pow n).natDegree_mul hp, hn, Nat.succ_mul, add_comm]

end Monic

@[simp]
/--
theorem `natDegree_pow_X_add_C` / 定理 `natDegree_pow_X_add_C`

English:
theorem natDegree_pow_X_add_C
  given: [Nontrivial R] (n : Nat) (r : R)
  statement: ((X + C r) ^ n).natDegree = n
  proof: by
  rw [(monic_X_add_C r).natDegree_pow]; rw [natDegree_X_add_C]; rw [mul_one]

中文:
定理 natDegree_pow_X_add_C
  条件: [非平凡 R] (n : 自然数) (r : R)
  结论: ((X + C r) ^ n).natDegree = n
  证明: by
  rw [(monic_X_add_C r).natDegree_pow]; rw [natDegree_X_add_C]; rw [mul_one]

Depends on / 依赖: monic_X_add_C, mul_one, natDegree_X_add_C, natDegree_pow
-/
theorem natDegree_pow_X_add_C [Nontrivial R] (n : Nat) (r : R) : ((X + C r) ^ n).natDegree = n := by
  rw [(monic_X_add_C r).natDegree_pow]; rw [natDegree_X_add_C]; rw [mul_one]

/--
theorem `Monic.eq_one_of_isUnit` / 定理 `Monic.eq_one_of_isUnit`

English:
theorem Monic.eq_one_of_isUnit
  given: (hm : Monic p) (hpu : IsUnit p)
  statement: p = 1
  proof: by
  nontriviality R
  obtain ⟨q, h⟩ := hpu.exists_right_inv
  have := hm.natDegree_mul' (right_ne_zero_of_mul_eq_one h)
  rw [h]; rw [natDegree_one]; rw [eq_comm]; rw [add_eq_zero] at this
  exact hm.natDegree_eq_zero.mp this.1

中文:
定理 Monic.eq_one_of_isUnit
  条件: (hm : Monic p) (hpu : 是单位 p)
  结论: p = 1
  证明: by
  nontriviality R
  obtain ⟨q, h⟩ := hpu.exists_right_inv
  have := hm.natDegree_mul' (right_ne_zero_of_mul_eq_one h)
  rw [h]; rw [natDegree_one]; rw [eq_comm]; rw [add_eq_zero] at this
  exact hm.natDegree_eq_zero.mp this.1

Depends on / 依赖: add_eq_zero, eq_comm, exists_right_inv, hm.natDegree_eq_zero.mp, hm.natDegree_mul, hpu.exists_right_inv, natDegree_eq_zero, natDegree_mul, natDegree_one, nontriviality, right_ne_zero_of_mul_eq_one
-/
theorem Monic.eq_one_of_isUnit (hm : Monic p) (hpu : IsUnit p) : p = 1 := by
  nontriviality R
  obtain ⟨q, h⟩ := hpu.exists_right_inv
  have := hm.natDegree_mul' (right_ne_zero_of_mul_eq_one h)
  rw [h]; rw [natDegree_one]; rw [eq_comm]; rw [add_eq_zero] at this
  exact hm.natDegree_eq_zero.mp this.1

/--
theorem `Monic.isUnit_iff` / 定理 `Monic.isUnit_iff`

English:
theorem Monic.isUnit_iff
  given: (hm : p.Monic)
  statement: IsUnit p ↔ p = 1
  proof: ⟨hm.eq_one_of_isUnit, fun h => h.symm ▸ isUnit_one⟩

中文:
定理 Monic.isUnit_iff
  条件: (hm : p.Monic)
  结论: 是单位 p ↔ p = 1
  证明: ⟨hm.eq_one_of_isUnit, fun h => h.symm ▸ isUnit_one⟩

Depends on / 依赖: eq_one_of_isUnit, h.symm, hm.eq_one_of_isUnit, isUnit_one
-/
theorem Monic.isUnit_iff (hm : p.Monic) : IsUnit p ↔ p = 1 :=
  ⟨hm.eq_one_of_isUnit, fun h => h.symm ▸ isUnit_one⟩

/--
theorem `eq_of_monic_of_associated` / 定理 `eq_of_monic_of_associated`

English:
theorem eq_of_monic_of_associated
  given: (hp : p.Monic) (hq : q.Monic) (hpq : Associated p q)
  statement: p = q
  proof: by
  obtain ⟨u, rfl⟩ := hpq
  rw [(hp.of_mul_monic_left hq).eq_one_of_isUnit u.isUnit]; rw [mul_one]

中文:
定理 eq_of_monic_of_associated
  条件: (hp : p.Monic) (hq : q.Monic) (hpq : Associated p q)
  结论: p = q
  证明: by
  obtain ⟨u, rfl⟩ := hpq
  rw [(hp.of_mul_monic_left hq).eq_one_of_isUnit u.isUnit]; rw [mul_one]

Depends on / 依赖: eq_one_of_isUnit, hp.of_mul_monic_left, isUnit, mul_one, of_mul_monic_left, u.isUnit
-/
theorem eq_of_monic_of_associated (hp : p.Monic) (hq : q.Monic) (hpq : Associated p q) : p = q := by
  obtain ⟨u, rfl⟩ := hpq
  rw [(hp.of_mul_monic_left hq).eq_one_of_isUnit u.isUnit]; rw [mul_one]

section MonicDegreeEq

variable [Semiring S]

variable (R n) in
/--
Definition of `MonicDegreeEq` / `MonicDegreeEq` 的定义

English:
abbreviation MonicDegreeEq
  signature: : Type _
  body: { p : R[X] // p.coeff n = 1 ∧ forall i > n, p.coeff i = 0 }

@[simp]

中文:
缩写 MonicDegreeEq
  签名: : 类型 _
  定义体: { p : R[X] // p.coeff n = 1 ∧ forall i > n, p.coeff i = 0 }

@[simp]

Depends on / 依赖: p.coeff
-/
abbrev MonicDegreeEq : Type _ := { p : R[X] // p.coeff n = 1 ∧ forall i > n, p.coeff i = 0 }

@[simp]
/--
lemma `MonicDegreeEq.natDegree` / 引理 `MonicDegreeEq.natDegree`

English:
lemma MonicDegreeEq.natDegree
  given: [Nontrivial R] (p : MonicDegreeEq R n)
  proof: natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr p.2.2) (by simp [p.2.1])

@[simp]

中文:
引理 MonicDegreeEq.natDegree
  条件: [非平凡 R] (p : MonicDegreeEq R n)
  证明: natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr p.2.2) (by simp [p.2.1])

@[simp]

Depends on / 依赖: natDegree_eq_of_le_of_coeff_ne_zero, natDegree_le_iff_coeff_eq_zero, natDegree_le_iff_coeff_eq_zero.mpr
-/
lemma MonicDegreeEq.natDegree [Nontrivial R] (p : MonicDegreeEq R n) :
    p.1.natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr p.2.2) (by simp [p.2.1])

@[simp]
/--
lemma `MonicDegreeEq.degree` / 引理 `MonicDegreeEq.degree`

English:
lemma MonicDegreeEq.degree
  given: [Nontrivial R] (p : MonicDegreeEq R n)
  proof: degree_eq_of_le_of_coeff_ne_zero (degree_le_of_natDegree_le p.natDegree.le) (by simp [p.2.1])

中文:
引理 MonicDegreeEq.degree
  条件: [非平凡 R] (p : MonicDegreeEq R n)
  证明: degree_eq_of_le_of_coeff_ne_zero (degree_le_of_natDegree_le p.natDegree.le) (by simp [p.2.1])

Depends on / 依赖: degree_eq_of_le_of_coeff_ne_zero, degree_le_of_natDegree_le, natDegree, p.natDegree.le
-/
lemma MonicDegreeEq.degree [Nontrivial R] (p : MonicDegreeEq R n) :
    p.1.degree = n :=
  degree_eq_of_le_of_coeff_ne_zero (degree_le_of_natDegree_le p.natDegree.le) (by simp [p.2.1])

/--
lemma `MonicDegreeEq.monic` / 引理 `MonicDegreeEq.monic`

English:
lemma MonicDegreeEq.monic
  given: (p : MonicDegreeEq R n)
  proof: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff]; rw [p.natDegree]; rw [p.2.1]

中文:
引理 MonicDegreeEq.monic
  条件: (p : MonicDegreeEq R n)
  证明: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff]; rw [p.natDegree]; rw [p.2.1]

Depends on / 依赖: leadingCoeff, natDegree, nontriviality, p.natDegree
-/
lemma MonicDegreeEq.monic (p : MonicDegreeEq R n) :
    p.1.Monic := by
  nontriviality R
  rw [Monic]; rw [leadingCoeff]; rw [p.natDegree]; rw [p.2.1]

/--
lemma `MonicDegreeEq.coeff_of_ge` / 引理 `MonicDegreeEq.coeff_of_ge`

English:
lemma MonicDegreeEq.coeff_of_ge
  given: (p : MonicDegreeEq R n) (i : Nat) (hi : n <= i)
  proof: by
  split_ifs <;> simp_all [p.2.1, p.2.2 _ (hi.lt_of_ne (.symm _))]

中文:
引理 MonicDegreeEq.coeff_of_ge
  条件: (p : MonicDegreeEq R n) (i : 自然数) (hi : n <= i)
  证明: by
  split_ifs <;> simp_all [p.2.1, p.2.2 _ (hi.lt_of_ne (.symm _))]

Depends on / 依赖: hi.lt_of_ne, lt_of_ne, split_ifs
-/
lemma MonicDegreeEq.coeff_of_ge (p : MonicDegreeEq R n) (i : Nat) (hi : n <= i) :
    p.1.coeff i = if i = n then 1 else 0 := by
  split_ifs <;> simp_all [p.2.1, p.2.2 _ (hi.lt_of_ne (.symm _))]

/-- The constructor for `MonicDegreeEq` given a monic polynomial of degree `n`. -/
@[simps]
/--
Definition of `MonicDegreeEq.mk` / `MonicDegreeEq.mk` 的定义

English:
definition MonicDegreeEq.mk
  signature: (p : R[X]) (hp : p.Monic) (hp' : p.natDegree = n)
  body: ⟨p, by rw [← hp', ← leadingCoeff, hp], fun i hi => coeff_eq_zero_of_natDegree_lt (hp'.trans_lt hi)⟩

中文:
定义 MonicDegreeEq.mk
  签名: (p : R[X]) (hp : p.Monic) (hp' : p.natDegree = n)
  定义体: ⟨p, by rw [← hp', ← leadingCoeff, hp], fun i hi => coeff_eq_zero_of_natDegree_lt (hp'.trans_lt hi)⟩

Depends on / 依赖: coeff_eq_zero_of_natDegree_lt, leadingCoeff, trans_lt
-/
def MonicDegreeEq.mk (p : R[X]) (hp : p.Monic) (hp' : p.natDegree = n) :
    MonicDegreeEq R n :=
  ⟨p, by rw [← hp', ← leadingCoeff, hp], fun i hi => coeff_eq_zero_of_natDegree_lt (hp'.trans_lt hi)⟩

/-- The image of a monic polynomial of degree `n` under a ring homomorphism. -/
@[simps] noncomputable
/--
Definition of `MonicDegreeEq.map` / `MonicDegreeEq.map` 的定义

English:
definition MonicDegreeEq.map
  signature: (p : MonicDegreeEq R n) (f : R ->+* S)
  body: ⟨p.1.map f, by simp +contextual [coeff_map, p.2]⟩

中文:
定义 MonicDegreeEq.map
  签名: (p : MonicDegreeEq R n) (f : R ->+* S)
  定义体: ⟨p.1.map f, by simp +contextual [coeff_map, p.2]⟩

Depends on / 依赖: coeff_map, contextual
-/
def MonicDegreeEq.map (p : MonicDegreeEq R n) (f : R ->+* S) :
    MonicDegreeEq S n :=
  ⟨p.1.map f, by simp +contextual [coeff_map, p.2]⟩

end MonicDegreeEq

end Semiring

section CommSemiring

variable [CommSemiring R] {p : R[X]}

/--
theorem `monic_multiset_prod_of_monic` / 定理 `monic_multiset_prod_of_monic`

English:
theorem monic_multiset_prod_of_monic
  given: (t : Multiset ι) (f : ι -> R[X]) (ht : forall i in t, Monic (f i))
  proof: by
  revert ht
  refine t.induction_on ?_ ?_; · simp
  intro a t ih ht
  rw [Multiset.map_cons]; rw [Multiset.prod_cons]
  exact (ht _ (Multiset.mem_cons_self _ _)).mul (ih fun _ hi => ht _ (Multiset.mem_cons_of_mem hi))

中文:
定理 monic_multiset_prod_of_monic
  条件: (t : Multiset ι) (f : ι -> R[X]) (ht : 对任意 i in t, Monic (f i))
  证明: by
  revert ht
  refine t.induction_on ?_ ?_; · simp
  intro a t ih ht
  rw [Multiset.map_cons]; rw [Multiset.prod_cons]
  exact (ht _ (Multiset.mem_cons_self _ _)).mul (ih fun _ hi => ht _ (Multiset.mem_cons_of_mem hi))

Depends on / 依赖: Multiset, Multiset.map_cons, Multiset.mem_cons_of_mem, Multiset.mem_cons_self, Multiset.prod_cons, induction_on, map_cons, mem_cons_of_mem, mem_cons_self, prod_cons, revert, t.induction_on
-/
theorem monic_multiset_prod_of_monic (t : Multiset ι) (f : ι -> R[X]) (ht : forall i in t, Monic (f i)) :
    Monic (t.map f).prod := by
  revert ht
  refine t.induction_on ?_ ?_; · simp
  intro a t ih ht
  rw [Multiset.map_cons]; rw [Multiset.prod_cons]
  exact (ht _ (Multiset.mem_cons_self _ _)).mul (ih fun _ hi => ht _ (Multiset.mem_cons_of_mem hi))

/--
theorem `monic_prod_of_monic` / 定理 `monic_prod_of_monic`

English:
theorem monic_prod_of_monic
  given: (s : Finset ι) (f : ι -> R[X]) (hs : forall i in s, Monic (f i))
  proof: monic_multiset_prod_of_monic s.1 f hs

中文:
定理 monic_prod_of_monic
  条件: (s : 有限集 ι) (f : ι -> R[X]) (hs : 对任意 i in s, Monic (f i))
  证明: monic_multiset_prod_of_monic s.1 f hs

Depends on / 依赖: monic_multiset_prod_of_monic
-/
theorem monic_prod_of_monic (s : Finset ι) (f : ι -> R[X]) (hs : forall i in s, Monic (f i)) :
    Monic (∏ i in s, f i) :=
  monic_multiset_prod_of_monic s.1 f hs

/--
theorem `monic_finprod_of_monic` / 定理 `monic_finprod_of_monic`

English:
theorem monic_finprod_of_monic
  statement: (α : Type*) (f : α -> R[X])
  proof: by
  classical
  rw [finprod_def]
  split_ifs
  · exact monic_prod_of_monic _ _ fun a ha => hf a ((Set.Finite.mem_toFinset _).mp ha)
  · exact monic_one

中文:
定理 monic_finprod_of_monic
  结论: (α : 类型) (f : α -> R[X])
  证明: by
  classical
  rw [finprod_def]
  split_ifs
  · exact monic_prod_of_monic _ _ fun a ha => hf a ((Set.Finite.mem_toFinset _).mp ha)
  · exact monic_one

Depends on / 依赖: Finite, Set.Finite.mem_toFinset, classical, finprod_def, mem_toFinset, monic_one, monic_prod_of_monic, split_ifs
-/
theorem monic_finprod_of_monic (α : Type*) (f : α -> R[X])
    (hf : forall i in Function.mulSupport f, Monic (f i)) :
    Monic (finprod f) := by
  classical
  rw [finprod_def]
  split_ifs
  · exact monic_prod_of_monic _ _ fun a ha => hf a ((Set.Finite.mem_toFinset _).mp ha)
  · exact monic_one

/--
theorem `Monic.nextCoeff_multiset_prod` / 定理 `Monic.nextCoeff_multiset_prod`

English:
theorem Monic.nextCoeff_multiset_prod
  given: (t : Multiset ι) (f : ι -> R[X]) (h : forall i in t, Monic (f i))
  proof: by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_
  · simp only [Multiset.notMem_zero, forall_prop_of_true, forall_prop_of_false, Multiset.map_zero,
      Multiset.prod_zero, Multiset.sum_zero, not_false_iff, forall_true_iff]
    rw [← C_1]
    rw [nextCoeff_C_eq_zero]
  · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      Monic.nextCoeff_mul, ih]
    exacts [fun i hi => ht i (Multiset.mem_cons_of_mem hi), ht a (Multiset.mem_cons_self _ _),
      monic_multiset_prod_of_monic _ _ fun b bs => ht _ (Multiset.mem_cons_of_mem bs)]

中文:
定理 Monic.nextCoeff_multiset_prod
  条件: (t : Multiset ι) (f : ι -> R[X]) (h : 对任意 i in t, Monic (f i))
  证明: by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_
  · simp only [Multiset.notMem_zero, forall_prop_of_true, forall_prop_of_false, Multiset.map_zero,
      Multiset.prod_zero, Multiset.sum_zero, not_false_iff, forall_true_iff]
    rw [← C_1]
    rw [nextCoeff_C_eq_zero]
  · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      Monic.nextCoeff_mul, ih]
    exacts [fun i hi => ht i (Multiset.mem_cons_of_mem hi), ht a (Multiset.mem_cons_self _ _),
      monic_multiset_prod_of_monic _ _ fun b bs => ht _ (Multiset.mem_cons_of_mem bs)]

Depends on / 依赖: Monic.nextCoeff_mul, Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.map_zero, Multiset.mem_cons_of_mem, Multiset.mem_cons_self, Multiset.notMem_zero, Multiset.prod_cons, Multiset.prod_zero, Multiset.sum_cons, Multiset.sum_zero, exacts, forall_prop_of_false, forall_prop_of_true, forall_true_iff, induction_on, map_cons, map_zero, mem_cons_of_mem
-/
theorem Monic.nextCoeff_multiset_prod (t : Multiset ι) (f : ι -> R[X]) (h : forall i in t, Monic (f i)) :
    nextCoeff (t.map f).prod = (t.map fun i => nextCoeff (f i)).sum := by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_
  · simp only [Multiset.notMem_zero, forall_prop_of_true, forall_prop_of_false, Multiset.map_zero,
      Multiset.prod_zero, Multiset.sum_zero, not_false_iff, forall_true_iff]
    rw [← C_1]
    rw [nextCoeff_C_eq_zero]
  · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      Monic.nextCoeff_mul, ih]
    exacts [fun i hi => ht i (Multiset.mem_cons_of_mem hi), ht a (Multiset.mem_cons_self _ _),
      monic_multiset_prod_of_monic _ _ fun b bs => ht _ (Multiset.mem_cons_of_mem bs)]

/--
theorem `Monic.nextCoeff_prod` / 定理 `Monic.nextCoeff_prod`

English:
theorem Monic.nextCoeff_prod
  given: (s : Finset ι) (f : ι -> R[X]) (h : forall i in s, Monic (f i))
  proof: Monic.nextCoeff_multiset_prod s.1 f h

中文:
定理 Monic.nextCoeff_prod
  条件: (s : 有限集 ι) (f : ι -> R[X]) (h : 对任意 i in s, Monic (f i))
  证明: Monic.nextCoeff_multiset_prod s.1 f h

Depends on / 依赖: Monic.nextCoeff_multiset_prod, nextCoeff_multiset_prod
-/
theorem Monic.nextCoeff_prod (s : Finset ι) (f : ι -> R[X]) (h : forall i in s, Monic (f i)) :
    nextCoeff (∏ i in s, f i) = ∑ i in s, nextCoeff (f i) :=
  Monic.nextCoeff_multiset_prod s.1 f h

variable [NoZeroDivisors R] {p q : R[X]}

/--
lemma `irreducible_of_monic` / 引理 `irreducible_of_monic`

English:
lemma irreducible_of_monic
  given: (hp : p.Monic) (hp1 : p != 1)
  proof: by
  refine
    ⟨fun h f g hf hg hp => (h.2 hp.symm).imp hf.eq_one_of_isUnit hg.eq_one_of_isUnit, fun h =>
      ⟨hp1 ∘ hp.eq_one_of_isUnit, fun f g hfg =>
        (h (g * C f.leadingCoeff) (f * C g.leadingCoeff) ?_ ?_ ?_).symm.imp
          (.of_mul_eq_one _)
          (.of_mul_eq_one _)⟩⟩
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, mul_comm, ← hfg, ← Monic]
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, ← hfg, ← Monic]
  · rw [mul_mul_mul_comm, ← C_mul, ← leadingCoeff_mul, ← hfg, hp.leadingCoeff, C_1, mul_one,
      mul_comm, ← hfg]

中文:
引理 irreducible_of_monic
  条件: (hp : p.Monic) (hp1 : p != 1)
  证明: by
  refine
    ⟨fun h f g hf hg hp => (h.2 hp.symm).imp hf.eq_one_of_isUnit hg.eq_one_of_isUnit, fun h =>
      ⟨hp1 ∘ hp.eq_one_of_isUnit, fun f g hfg =>
        (h (g * C f.leadingCoeff) (f * C g.leadingCoeff) ?_ ?_ ?_).symm.imp
          (.of_mul_eq_one _)
          (.of_mul_eq_one _)⟩⟩
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, mul_comm, ← hfg, ← Monic]
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, ← hfg, ← Monic]
  · rw [mul_mul_mul_comm, ← C_mul, ← leadingCoeff_mul, ← hfg, hp.leadingCoeff, C_1, mul_one,
      mul_comm, ← hfg]

Depends on / 依赖: C_mul, eq_one_of_isUnit, f.leadingCoeff, g.leadingCoeff, hf.eq_one_of_isUnit, hg.eq_one_of_isUnit, hp.eq_one_of_isUnit, hp.leading, hp.symm, leading, leadingCoeff, leadingCoeff_C, leadingCoeff_mul, mul_comm, mul_mul_mul_comm, of_mul_eq_one, symm.imp
-/
lemma irreducible_of_monic (hp : p.Monic) (hp1 : p != 1) :
    Irreducible p ↔ forall f g : R[X], f.Monic -> g.Monic -> f * g = p -> f = 1 ∨ g = 1 := by
  refine
    ⟨fun h f g hf hg hp => (h.2 hp.symm).imp hf.eq_one_of_isUnit hg.eq_one_of_isUnit, fun h =>
      ⟨hp1 ∘ hp.eq_one_of_isUnit, fun f g hfg =>
        (h (g * C f.leadingCoeff) (f * C g.leadingCoeff) ?_ ?_ ?_).symm.imp
          (.of_mul_eq_one _)
          (.of_mul_eq_one _)⟩⟩
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, mul_comm, ← hfg, ← Monic]
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, ← hfg, ← Monic]
  · rw [mul_mul_mul_comm, ← C_mul, ← leadingCoeff_mul, ← hfg, hp.leadingCoeff, C_1, mul_one,
      mul_comm, ← hfg]


/--
lemma `Monic.irreducible_iff_natDegree` / 引理 `Monic.irreducible_iff_natDegree`

English:
lemma Monic.irreducible_iff_natDegree
  given: (hp : p.Monic)
  proof: by
  by_cases hp1 : p = 1; · simp [hp1]
  rw [irreducible_of_monic hp hp1]; rw [and_iff_right hp1]
  refine forall₄_congr fun a b ha hb => ?_
  rw [ha.natDegree_eq_zero]; rw [hb.natDegree_eq_zero]

中文:
引理 Monic.irreducible_iff_natDegree
  条件: (hp : p.Monic)
  证明: by
  by_cases hp1 : p = 1; · simp [hp1]
  rw [irreducible_of_monic hp hp1]; rw [and_iff_right hp1]
  refine forall₄_congr fun a b ha hb => ?_
  rw [ha.natDegree_eq_zero]; rw [hb.natDegree_eq_zero]

Depends on / 依赖: and_iff_right, ha.natDegree_eq_zero, hb.natDegree_eq_zero, irreducible_of_monic, natDegree_eq_zero
-/
lemma Monic.irreducible_iff_natDegree (hp : p.Monic) :
    Irreducible p ↔
      p != 1 ∧ forall f g : R[X], f.Monic -> g.Monic -> f * g = p -> f.natDegree = 0 ∨ g.natDegree = 0 := by
  by_cases hp1 : p = 1; · simp [hp1]
  rw [irreducible_of_monic hp hp1]; rw [and_iff_right hp1]
  refine forall₄_congr fun a b ha hb => ?_
  rw [ha.natDegree_eq_zero]; rw [hb.natDegree_eq_zero]

/--
lemma `Monic.irreducible_iff_natDegree'` / 引理 `Monic.irreducible_iff_natDegree'`

English:
lemma Monic.irreducible_iff_natDegree'
  given: (hp : p.Monic)
  statement: Irreducible p ↔ p != 1 ∧
  proof: by
  simp_rw [hp.irreducible_iff_natDegree, mem_Ioc, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  apply and_congr_right'
  constructor <;> intro h f g hf hg he <;> subst he
  · rw [hf.natDegree_mul hg, add_le_add_iff_right]
    exact fun ha => (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne'
  · simp_rw [hf.natDegree_mul hg, pos_iff_ne_zero] at h
    contrapose! h
    obtain hl | hl := le_total f.natDegree g.natDegree
    · exact ⟨g, f, hg, hf, mul_comm g f, h.1, by gcongr⟩
    · exact ⟨f, g, hf, hg, rfl, h.2, by gcongr⟩

中文:
引理 Monic.irreducible_iff_natDegree'
  条件: (hp : p.Monic)
  结论: 不可约 p ↔ p != 1 ∧
  证明: by
  simp_rw [hp.irreducible_iff_natDegree, mem_Ioc, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  apply and_congr_right'
  constructor <;> intro h f g hf hg he <;> subst he
  · rw [hf.natDegree_mul hg, add_le_add_iff_right]
    exact fun ha => (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne'
  · simp_rw [hf.natDegree_mul hg, pos_iff_ne_zero] at h
    contrapose! h
    obtain hl | hl := le_total f.natDegree g.natDegree
    · exact ⟨g, f, hg, hf, mul_comm g f, h.1, by gcongr⟩
    · exact ⟨f, g, hf, hg, rfl, h.2, by gcongr⟩

Depends on / 依赖: Nat.le_div_iff_mul_le, add_le_add_iff_right, and_congr_right, contrapose, f.natDegree, g.natDegree, hf.natDegree_mul, hp.irreducible_iff_natDegree, irreducible_iff_natDegree, le_div_iff_mul_le, le_total, mem_Ioc, mul_comm, mul_two, natDegree, natDegree_mul, pos_iff_ne_zero, simp_rw, trans_le, zero_lt_two
-/
lemma Monic.irreducible_iff_natDegree' (hp : p.Monic) : Irreducible p ↔ p != 1 ∧
    forall f g : R[X], f.Monic -> g.Monic -> f * g = p -> g.natDegree ∉ Ioc 0 (p.natDegree / 2) := by
  simp_rw [hp.irreducible_iff_natDegree, mem_Ioc, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  apply and_congr_right'
  constructor <;> intro h f g hf hg he <;> subst he
  · rw [hf.natDegree_mul hg, add_le_add_iff_right]
    exact fun ha => (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne'
  · simp_rw [hf.natDegree_mul hg, pos_iff_ne_zero] at h
    contrapose! h
    obtain hl | hl := le_total f.natDegree g.natDegree
    · exact ⟨g, f, hg, hf, mul_comm g f, h.1, by gcongr⟩
    · exact ⟨f, g, hf, hg, rfl, h.2, by gcongr⟩

/--
lemma `Monic.irreducible_iff_lt_natDegree_lt` / 引理 `Monic.irreducible_iff_lt_natDegree_lt`

English:
lemma Monic.irreducible_iff_lt_natDegree_lt
  given: {p : R[X]} (hp : p.Monic) (hp1 : p != 1)
  proof: by
  rw [hp.irreducible_iff_natDegree']; rw [and_iff_right hp1]
  constructor
  · rintro h g hg hdg ⟨f, rfl⟩
    exact h f g (hg.of_mul_monic_left hp) hg (mul_comm f g) hdg
  · rintro h f g - hg rfl hdg
    exact h g hg hdg (dvd_mul_left g f)

中文:
引理 Monic.irreducible_iff_lt_natDegree_lt
  条件: {p : R[X]} (hp : p.Monic) (hp1 : p != 1)
  证明: by
  rw [hp.irreducible_iff_natDegree']; rw [and_iff_right hp1]
  constructor
  · rintro h g hg hdg ⟨f, rfl⟩
    exact h f g (hg.of_mul_monic_left hp) hg (mul_comm f g) hdg
  · rintro h f g - hg rfl hdg
    exact h g hg hdg (dvd_mul_left g f)

Depends on / 依赖: and_iff_right, dvd_mul_left, hg.of_mul_monic_left, hp.irreducible_iff_natDegree, irreducible_iff_natDegree, mul_comm, of_mul_monic_left
-/
lemma Monic.irreducible_iff_lt_natDegree_lt {p : R[X]} (hp : p.Monic) (hp1 : p != 1) :
    Irreducible p ↔ forall q, Monic q -> natDegree q in Finset.Ioc 0 (natDegree p / 2) -> ¬ q ∣ p := by
  rw [hp.irreducible_iff_natDegree']; rw [and_iff_right hp1]
  constructor
  · rintro h g hg hdg ⟨f, rfl⟩
    exact h f g (hg.of_mul_monic_left hp) hg (mul_comm f g) hdg
  · rintro h f g - hg rfl hdg
    exact h g hg hdg (dvd_mul_left g f)

/--
lemma `Monic.not_irreducible_iff_exists_add_mul_eq_coeff` / 引理 `Monic.not_irreducible_iff_exists_add_mul_eq_coeff`

English:
lemma Monic.not_irreducible_iff_exists_add_mul_eq_coeff
  given: (hm : p.Monic) (hnd : p.natDegree = 2)
  proof: by
  cases subsingleton_or_nontrivial R
  · simp [natDegree_of_subsingleton] at hnd
  rw [hm.irreducible_iff_natDegree']; rw [and_iff_right]; rw [hnd]
  · push Not
    constructor
    · rintro ⟨a, b, ha, hb, rfl, hdb⟩
      simp only [Nat.Ioc_succ_singleton, zero_add, mem_singleton] at hdb
      have hda := hnd
      rw [ha.natDegree_mul hb]; rw [hdb] at hda
      use a.coeff 0, b.coeff 0, mul_coeff_zero a b
      simpa only [nextCoeff, hnd, add_right_cancel hda, hdb] using! ha.nextCoeff_mul hb
    · rintro ⟨c₁, c₂, hmul, hadd⟩
      refine
        ⟨X + C c₁, X + C c₂, monic_X_add_C _, monic_X_add_C _, ?_, ?_⟩
      · rw [p.as_sum_range_C_mul_X_pow, hnd, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_one, ← hnd, hm.coeff_natDegree, hnd, hmul, hadd, C_mul, C_add, C_1]
        ring
      · simp
  · rintro rfl
    simp [natDegree_one] at hnd

中文:
引理 Monic.not_irreducible_iff_存在_add_mul_eq_coeff
  条件: (hm : p.Monic) (hnd : p.natDegree = 2)
  证明: by
  cases subsingleton_or_nontrivial R
  · simp [natDegree_of_subsingleton] at hnd
  rw [hm.irreducible_iff_natDegree']; rw [and_iff_right]; rw [hnd]
  · push Not
    constructor
    · rintro ⟨a, b, ha, hb, rfl, hdb⟩
      simp only [Nat.Ioc_succ_singleton, zero_add, mem_singleton] at hdb
      have hda := hnd
      rw [ha.natDegree_mul hb]; rw [hdb] at hda
      use a.coeff 0, b.coeff 0, mul_coeff_zero a b
      simpa only [nextCoeff, hnd, add_right_cancel hda, hdb] using! ha.nextCoeff_mul hb
    · rintro ⟨c₁, c₂, hmul, hadd⟩
      refine
        ⟨X + C c₁, X + C c₂, monic_X_add_C _, monic_X_add_C _, ?_, ?_⟩
      · rw [p.as_sum_range_C_mul_X_pow, hnd, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_one, ← hnd, hm.coeff_natDegree, hnd, hmul, hadd, C_mul, C_add, C_1]
        ring
      · simp
  · rintro rfl
    simp [natDegree_one] at hnd

Depends on / 依赖: Ioc_succ_singleton, Nat.Ioc_succ_singleton, a.coeff, add_right_cancel, and_iff_right, b.coeff, ha.natDegree_mul, ha.nextCoeff_mul, hm.irreducible_iff_natDegree, irreducible_iff_natDegree, mem_singleton, mul_coeff_zero, natDegree_mul, natDegree_of_subsingleton, nextCoeff, nextCoeff_mul, subsingleton_or_nontrivial, zero_add
-/
lemma Monic.not_irreducible_iff_exists_add_mul_eq_coeff (hm : p.Monic) (hnd : p.natDegree = 2) :
    ¬Irreducible p ↔ exists c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂ := by
  cases subsingleton_or_nontrivial R
  · simp [natDegree_of_subsingleton] at hnd
  rw [hm.irreducible_iff_natDegree']; rw [and_iff_right]; rw [hnd]
  · push Not
    constructor
    · rintro ⟨a, b, ha, hb, rfl, hdb⟩
      simp only [Nat.Ioc_succ_singleton, zero_add, mem_singleton] at hdb
      have hda := hnd
      rw [ha.natDegree_mul hb]; rw [hdb] at hda
      use a.coeff 0, b.coeff 0, mul_coeff_zero a b
      simpa only [nextCoeff, hnd, add_right_cancel hda, hdb] using! ha.nextCoeff_mul hb
    · rintro ⟨c₁, c₂, hmul, hadd⟩
      refine
        ⟨X + C c₁, X + C c₂, monic_X_add_C _, monic_X_add_C _, ?_, ?_⟩
      · rw [p.as_sum_range_C_mul_X_pow, hnd, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_one, ← hnd, hm.coeff_natDegree, hnd, hmul, hadd, C_mul, C_add, C_1]
        ring
      · simp
  · rintro rfl
    simp [natDegree_one] at hnd

end CommSemiring

section Semiring

variable [Semiring R]

@[simp]
/--
theorem `Monic.natDegree_map` / 定理 `Monic.natDegree_map`

English:
theorem Monic.natDegree_map
  given: [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R ->+* S)
  proof: by
  refine le_antisymm natDegree_map_le (le_natDegree_of_ne_zero ?_)
  rw [coeff_map]; rw [Monic.coeff_natDegree hmo]; rw [map_one]
  exact one_ne_zero

@[simp]

中文:
定理 Monic.natDegree_map
  条件: [半环 S] [非平凡 S] {P : R[X]} (hmo : P.Monic) (f : R ->+* S)
  证明: by
  refine le_antisymm natDegree_map_le (le_natDegree_of_ne_zero ?_)
  rw [coeff_map]; rw [Monic.coeff_natDegree hmo]; rw [map_one]
  exact one_ne_zero

@[simp]

Depends on / 依赖: Monic.coeff_natDegree, coeff_map, coeff_natDegree, le_antisymm, le_natDegree_of_ne_zero, map_one, natDegree_map_le, one_ne_zero
-/
theorem Monic.natDegree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R ->+* S) :
    (P.map f).natDegree = P.natDegree := by
  refine le_antisymm natDegree_map_le (le_natDegree_of_ne_zero ?_)
  rw [coeff_map]; rw [Monic.coeff_natDegree hmo]; rw [map_one]
  exact one_ne_zero

@[simp]
/--
theorem `Monic.degree_map` / 定理 `Monic.degree_map`

English:
theorem Monic.degree_map
  given: [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R ->+* S)
  proof: by
  simp_all

中文:
定理 Monic.degree_map
  条件: [半环 S] [非平凡 S] {P : R[X]} (hmo : P.Monic) (f : R ->+* S)
  证明: by
  simp_all
-/
theorem Monic.degree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R ->+* S) :
    (P.map f).degree = P.degree := by
  simp_all

section Injective

open Function

variable [Semiring S] {f : R ->+* S}

/--
theorem `monic_of_injective` / 定理 `monic_of_injective`

English:
theorem monic_of_injective
  given: (hf : Injective f) {p : R[X]} (hp : (p.map f).Monic)
  statement: p.Monic
  proof: by
  apply hf
  rw [← leadingCoeff_map_of_injective hf]; rw [hp.leadingCoeff]; rw [f.map_one]

中文:
定理 monic_of_injective
  条件: (hf : 单射 f) {p : R[X]} (hp : (p.map f).Monic)
  结论: p.Monic
  证明: by
  apply hf
  rw [← leadingCoeff_map_of_injective hf]; rw [hp.leadingCoeff]; rw [f.map_one]

Depends on / 依赖: f.map_one, hp.leadingCoeff, leadingCoeff, leadingCoeff_map_of_injective, map_one
-/
theorem monic_of_injective (hf : Injective f) {p : R[X]} (hp : (p.map f).Monic) : p.Monic := by
  apply hf
  rw [← leadingCoeff_map_of_injective hf]; rw [hp.leadingCoeff]; rw [f.map_one]

/--
theorem `_root_.Function.Injective.monic_map_iff` / 定理 `_root_.Function.Injective.monic_map_iff`

English:
theorem _root_.Function.Injective.monic_map_iff
  given: (hf : Injective f) {p : R[X]}
  proof: ⟨Monic.map _, Polynomial.monic_of_injective hf⟩

中文:
定理 _root_.函数.单射.monic_map_iff
  条件: (hf : 单射 f) {p : R[X]}
  证明: ⟨Monic.map _, Polynomial.monic_of_injective hf⟩

Depends on / 依赖: Monic.map, Polynomial, Polynomial.monic_of_injective, monic_of_injective
-/
theorem _root_.Function.Injective.monic_map_iff (hf : Injective f) {p : R[X]} :
    p.Monic ↔ (p.map f).Monic :=
  ⟨Monic.map _, Polynomial.monic_of_injective hf⟩

end Injective

end Semiring

section Ring

variable [Ring R] {p : R[X]}

/--
theorem `monic_X_sub_C` / 定理 `monic_X_sub_C`

English:
theorem monic_X_sub_C
  given: (x : R)
  statement: Monic (X - C x)
  proof: by
  simpa only [sub_eq_add_neg, C_neg] using monic_X_add_C (-x)

中文:
定理 monic_X_sub_C
  条件: (x : R)
  结论: Monic (X - C x)
  证明: by
  simpa only [sub_eq_add_neg, C_neg] using monic_X_add_C (-x)

Depends on / 依赖: C_neg, monic_X_add_C, sub_eq_add_neg
-/
theorem monic_X_sub_C (x : R) : Monic (X - C x) := by
  simpa only [sub_eq_add_neg, C_neg] using monic_X_add_C (-x)

/--
theorem `monic_X_pow_sub` / 定理 `monic_X_pow_sub`

English:
theorem monic_X_pow_sub
  given: {n : Nat} (H : degree p < n)
  statement: Monic (X ^ n - p)
  proof: by
  simpa [sub_eq_add_neg] using monic_X_pow_add (show degree (-p) < n by rwa [← degree_neg p] at H)

中文:
定理 monic_X_pow_sub
  条件: {n : 自然数} (H : degree p < n)
  结论: Monic (X ^ n - p)
  证明: by
  simpa [sub_eq_add_neg] using monic_X_pow_add (show degree (-p) < n by rwa [← degree_neg p] at H)

Depends on / 依赖: degree, degree_neg, monic_X_pow_add, sub_eq_add_neg
-/
theorem monic_X_pow_sub {n : Nat} (H : degree p < n) : Monic (X ^ n - p) := by
  simpa [sub_eq_add_neg] using monic_X_pow_add (show degree (-p) < n by rwa [← degree_neg p] at H)

/--
theorem `monic_X_pow_sub_C` / 定理 `monic_X_pow_sub_C`

English:
theorem monic_X_pow_sub_C
  given: {R : Type u} [Ring R] (a : R) {n : Nat} (h : n != 0)
  proof: by
  simpa only [map_neg, ← sub_eq_add_neg] using monic_X_pow_add_C (-a) h

中文:
定理 monic_X_pow_sub_C
  条件: {R : 类型u} [环 R] (a : R) {n : 自然数} (h : n != 0)
  证明: by
  simpa only [map_neg, ← sub_eq_add_neg] using monic_X_pow_add_C (-a) h

Depends on / 依赖: map_neg, monic_X_pow_add_C, sub_eq_add_neg
-/
theorem monic_X_pow_sub_C {R : Type u} [Ring R] (a : R) {n : Nat} (h : n != 0) :
    (X ^ n - C a).Monic := by
  simpa only [map_neg, ← sub_eq_add_neg] using monic_X_pow_add_C (-a) h

/--
theorem `not_isUnit_X_pow_sub_one` / 定理 `not_isUnit_X_pow_sub_one`

English:
theorem not_isUnit_X_pow_sub_one
  given: (R : Type*) [Ring R] [Nontrivial R] (n : Nat)
  proof: by
  intro h
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp at h
  apply hn
  rw [← @natDegree_one R]; rw [← (monic_X_pow_sub_C _ hn).eq_one_of_isUnit h]; rw [natDegree_X_pow_sub_C]

中文:
定理 not_isUnit_X_pow_sub_one
  条件: (R : 类型) [环 R] [非平凡 R] (n : 自然数)
  证明: by
  intro h
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp at h
  apply hn
  rw [← @natDegree_one R]; rw [← (monic_X_pow_sub_C _ hn).eq_one_of_isUnit h]; rw [natDegree_X_pow_sub_C]

Depends on / 依赖: eq_one_of_isUnit, eq_or_ne, monic_X_pow_sub_C, natDegree_X_pow_sub_C, natDegree_one
-/
theorem not_isUnit_X_pow_sub_one (R : Type*) [Ring R] [Nontrivial R] (n : Nat) :
    ¬IsUnit (X ^ n - 1 : R[X]) := by
  intro h
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp at h
  apply hn
  rw [← @natDegree_one R]; rw [← (monic_X_pow_sub_C _ hn).eq_one_of_isUnit h]; rw [natDegree_X_pow_sub_C]

/--
lemma `Monic.comp_X_sub_C` / 引理 `Monic.comp_X_sub_C`

English:
lemma Monic.comp_X_sub_C
  given: {p : R[X]} (hp : p.Monic) (r : R)
  statement: (p.comp (X - C r)).Monic
  proof: by
  simpa using! hp.comp_X_add_C (-r)

中文:
引理 Monic.comp_X_sub_C
  条件: {p : R[X]} (hp : p.Monic) (r : R)
  结论: (p.comp (X - C r)).Monic
  证明: by
  simpa using! hp.comp_X_add_C (-r)

Depends on / 依赖: comp_X_add_C, hp.comp_X_add_C
-/
lemma Monic.comp_X_sub_C {p : R[X]} (hp : p.Monic) (r : R) : (p.comp (X - C r)).Monic := by
  simpa using! hp.comp_X_add_C (-r)

/--
theorem `Monic.sub_of_left` / 定理 `Monic.sub_of_left`

English:
theorem Monic.sub_of_left
  given: {p q : R[X]} (hp : Monic p) (hpq : degree q < degree p)
  proof: by
  rw [sub_eq_add_neg]
  apply hp.add_of_left
  rwa [degree_neg]

中文:
定理 Monic.sub_of_left
  条件: {p q : R[X]} (hp : Monic p) (hpq : degree q < degree p)
  证明: by
  rw [sub_eq_add_neg]
  apply hp.add_of_left
  rwa [degree_neg]

Depends on / 依赖: add_of_left, degree_neg, hp.add_of_left, sub_eq_add_neg
-/
theorem Monic.sub_of_left {p q : R[X]} (hp : Monic p) (hpq : degree q < degree p) :
    Monic (p - q) := by
  rw [sub_eq_add_neg]
  apply hp.add_of_left
  rwa [degree_neg]

/--
theorem `Monic.sub_of_right` / 定理 `Monic.sub_of_right`

English:
theorem Monic.sub_of_right
  given: {p q : R[X]} (hq : q.leadingCoeff = -1) (hpq : degree p < degree q)
  proof: by
  have : (-q).coeff (-q).natDegree = 1 := by
    rw [natDegree_neg]; rw [coeff_neg]; rw [show q.coeff q.natDegree = -1 from hq]; rw [neg_neg]
  rw [sub_eq_add_neg]
  apply Monic.add_of_right this
  rwa [degree_neg]

中文:
定理 Monic.sub_of_right
  条件: {p q : R[X]} (hq : q.leadingCoeff = -1) (hpq : degree p < degree q)
  证明: by
  have : (-q).coeff (-q).natDegree = 1 := by
    rw [natDegree_neg]; rw [coeff_neg]; rw [show q.coeff q.natDegree = -1 from hq]; rw [neg_neg]
  rw [sub_eq_add_neg]
  apply Monic.add_of_right this
  rwa [degree_neg]

Depends on / 依赖: Monic.add_of_right, add_of_right, coeff_neg, degree_neg, natDegree, natDegree_neg, neg_neg, q.coeff, q.natDegree, sub_eq_add_neg
-/
theorem Monic.sub_of_right {p q : R[X]} (hq : q.leadingCoeff = -1) (hpq : degree p < degree q) :
    Monic (p - q) := by
  have : (-q).coeff (-q).natDegree = 1 := by
    rw [natDegree_neg]; rw [coeff_neg]; rw [show q.coeff q.natDegree = -1 from hq]; rw [neg_neg]
  rw [sub_eq_add_neg]
  apply Monic.add_of_right this
  rwa [degree_neg]

end Ring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
/--
theorem `not_monic_zero` / 定理 `not_monic_zero`

English:
theorem not_monic_zero
  statement: ¬Monic (0 : R[X])
  proof: not_monic_zero_iff.mp zero_ne_one

中文:
定理 not_monic_zero
  结论: ¬Monic (0 : R[X])
  证明: not_monic_zero_iff.mp zero_ne_one

Depends on / 依赖: not_monic_zero_iff, not_monic_zero_iff.mp, zero_ne_one
-/
theorem not_monic_zero : ¬Monic (0 : R[X]) :=
  not_monic_zero_iff.mp zero_ne_one

end NonzeroSemiring

section NotZeroDivisor

-- TODO: using gh-8537, rephrase lemmas that involve commutation around `*` using the op-ring
variable [Semiring R] {p : R[X]}

/--
theorem `Monic.mul_left_ne_zero` / 定理 `Monic.mul_left_ne_zero`

English:
theorem Monic.mul_left_ne_zero
  given: (hp : Monic p) {q : R[X]} (hq : q != 0)
  statement: q * p != 0
  proof: by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne]; rw [← degree_eq_bot]; rw [hp.degree_mul]; rw [WithBot.add_eq_bot]; rw [not_or]; rw [degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one]; rw [not_le] at h
  refine (lt_trans ?_ h).ne'
  simp

中文:
定理 Monic.mul_left_ne_zero
  条件: (hp : Monic p) {q : R[X]} (hq : q != 0)
  结论: q * p != 0
  证明: by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne]; rw [← degree_eq_bot]; rw [hp.degree_mul]; rw [WithBot.add_eq_bot]; rw [not_or]; rw [degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one]; rw [not_le] at h
  refine (lt_trans ?_ h).ne'
  simp

Depends on / 依赖: WithBot, WithBot.add_eq_bot, add_eq_bot, degree_eq_bot, degree_le_zero_iff_eq_one, degree_mul, hp.degree_le_zero_iff_eq_one, hp.degree_mul, lt_trans, not_le, not_or
-/
theorem Monic.mul_left_ne_zero (hp : Monic p) {q : R[X]} (hq : q != 0) : q * p != 0 := by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne]; rw [← degree_eq_bot]; rw [hp.degree_mul]; rw [WithBot.add_eq_bot]; rw [not_or]; rw [degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one]; rw [not_le] at h
  refine (lt_trans ?_ h).ne'
  simp

/--
theorem `Monic.mul_right_ne_zero` / 定理 `Monic.mul_right_ne_zero`

English:
theorem Monic.mul_right_ne_zero
  given: (hp : Monic p) {q : R[X]} (hq : q != 0)
  statement: p * q != 0
  proof: by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne]; rw [← degree_eq_bot]; rw [hp.degree_mul_comm]; rw [hp.degree_mul]; rw [WithBot.add_eq_bot]; rw [not_or]; rw [degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one]; rw [not_le] at h
  refine (lt_trans ?_ h).ne'
  simp

中文:
定理 Monic.mul_right_ne_zero
  条件: (hp : Monic p) {q : R[X]} (hq : q != 0)
  结论: p * q != 0
  证明: by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne]; rw [← degree_eq_bot]; rw [hp.degree_mul_comm]; rw [hp.degree_mul]; rw [WithBot.add_eq_bot]; rw [not_or]; rw [degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one]; rw [not_le] at h
  refine (lt_trans ?_ h).ne'
  simp

Depends on / 依赖: WithBot, WithBot.add_eq_bot, add_eq_bot, degree_eq_bot, degree_le_zero_iff_eq_one, degree_mul, degree_mul_comm, hp.degree_le_zero_iff_eq_one, hp.degree_mul, hp.degree_mul_comm, lt_trans, not_le, not_or
-/
theorem Monic.mul_right_ne_zero (hp : Monic p) {q : R[X]} (hq : q != 0) : p * q != 0 := by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne]; rw [← degree_eq_bot]; rw [hp.degree_mul_comm]; rw [hp.degree_mul]; rw [WithBot.add_eq_bot]; rw [not_or]; rw [degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one]; rw [not_le] at h
  refine (lt_trans ?_ h).ne'
  simp

/--
theorem `Monic.mul_natDegree_lt_iff` / 定理 `Monic.mul_natDegree_lt_iff`

English:
theorem Monic.mul_natDegree_lt_iff
  given: (h : Monic p) {q : R[X]}
  proof: by
  by_cases hq : q = 0
  · suffices 0 < p.natDegree ↔ p.natDegree != 0 by simp [hq, ← h.natDegree_eq_zero, iffComm]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (Nat.zero_le _) h.symm⟩
  · simp [h.natDegree_mul', hq]

中文:
定理 Monic.mul_natDegree_lt_iff
  条件: (h : Monic p) {q : R[X]}
  证明: by
  by_cases hq : q = 0
  · suffices 0 < p.natDegree ↔ p.natDegree != 0 by simp [hq, ← h.natDegree_eq_zero, iffComm]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (Nat.zero_le _) h.symm⟩
  · simp [h.natDegree_mul', hq]

Depends on / 依赖: Nat.zero_le, h.natDegree_eq_zero, h.natDegree_mul, h.ne, h.symm, iffComm, lt_of_le_of_ne, natDegree, natDegree_eq_zero, natDegree_mul, p.natDegree, zero_le
-/
theorem Monic.mul_natDegree_lt_iff (h : Monic p) {q : R[X]} :
    (p * q).natDegree < p.natDegree ↔ p != 1 ∧ q = 0 := by
  by_cases hq : q = 0
  · suffices 0 < p.natDegree ↔ p.natDegree != 0 by simp [hq, ← h.natDegree_eq_zero, iffComm]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (Nat.zero_le _) h.symm⟩
  · simp [h.natDegree_mul', hq]

/--
theorem `Monic.mul_right_eq_zero_iff` / 定理 `Monic.mul_right_eq_zero_iff`

English:
theorem Monic.mul_right_eq_zero_iff
  given: (h : Monic p) {q : R[X]}
  statement: p * q = 0 ↔ q = 0
  proof: by
  by_cases hq : q = 0 <;> simp [h.mul_right_ne_zero, hq]

中文:
定理 Monic.mul_right_eq_zero_iff
  条件: (h : Monic p) {q : R[X]}
  结论: p * q = 0 ↔ q = 0
  证明: by
  by_cases hq : q = 0 <;> simp [h.mul_right_ne_zero, hq]

Depends on / 依赖: h.mul_right_ne_zero, mul_right_ne_zero
-/
theorem Monic.mul_right_eq_zero_iff (h : Monic p) {q : R[X]} : p * q = 0 ↔ q = 0 := by
  by_cases hq : q = 0 <;> simp [h.mul_right_ne_zero, hq]

/--
theorem `Monic.mul_left_eq_zero_iff` / 定理 `Monic.mul_left_eq_zero_iff`

English:
theorem Monic.mul_left_eq_zero_iff
  given: (h : Monic p) {q : R[X]}
  statement: q * p = 0 ↔ q = 0
  proof: by
  by_cases hq : q = 0 <;> simp [h.mul_left_ne_zero, hq]

中文:
定理 Monic.mul_left_eq_zero_iff
  条件: (h : Monic p) {q : R[X]}
  结论: q * p = 0 ↔ q = 0
  证明: by
  by_cases hq : q = 0 <;> simp [h.mul_left_ne_zero, hq]

Depends on / 依赖: h.mul_left_ne_zero, mul_left_ne_zero
-/
theorem Monic.mul_left_eq_zero_iff (h : Monic p) {q : R[X]} : q * p = 0 ↔ q = 0 := by
  by_cases hq : q = 0 <;> simp [h.mul_left_ne_zero, hq]

/--
theorem `Monic.isRegular` / 定理 `Monic.isRegular`

English:
theorem Monic.isRegular
  given: {R : Type*} [Ring R] {p : R[X]} (hp : Monic p)
  statement: IsRegular p
  proof: by
  constructor
  · intro q r h
    dsimp only at h
    rw [← sub_eq_zero]; rw [← hp.mul_right_eq_zero_iff]; rw [mul_sub]; rw [h]; rw [sub_self]
  · intro q r h
    simp only at h
    rw [← sub_eq_zero]; rw [← hp.mul_left_eq_zero_iff]; rw [sub_mul]; rw [h]; rw [sub_self]

中文:
定理 Monic.isRegular
  条件: {R : 类型} [环 R] {p : R[X]} (hp : Monic p)
  结论: 是正则 p
  证明: by
  constructor
  · intro q r h
    dsimp only at h
    rw [← sub_eq_zero]; rw [← hp.mul_right_eq_zero_iff]; rw [mul_sub]; rw [h]; rw [sub_self]
  · intro q r h
    simp only at h
    rw [← sub_eq_zero]; rw [← hp.mul_left_eq_zero_iff]; rw [sub_mul]; rw [h]; rw [sub_self]

Depends on / 依赖: hp.mul_left_eq_zero_iff, hp.mul_right_eq_zero_iff, mul_left_eq_zero_iff, mul_right_eq_zero_iff, mul_sub, sub_eq_zero, sub_mul, sub_self
-/
theorem Monic.isRegular {R : Type*} [Ring R] {p : R[X]} (hp : Monic p) : IsRegular p := by
  constructor
  · intro q r h
    dsimp only at h
    rw [← sub_eq_zero]; rw [← hp.mul_right_eq_zero_iff]; rw [mul_sub]; rw [h]; rw [sub_self]
  · intro q r h
    simp only at h
    rw [← sub_eq_zero]; rw [← hp.mul_left_eq_zero_iff]; rw [sub_mul]; rw [h]; rw [sub_self]

/--
theorem `degree_smul_of_smul_regular` / 定理 `degree_smul_of_smul_regular`

English:
theorem degree_smul_of_smul_regular
  statement: {S : Type*} [SMulZeroClass S R] {k : S}
  proof: by
  refine le_antisymm ?_ ?_
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    simp [hm m le_rfl]
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    refine h ?_
    simpa using hm m le_rfl

中文:
定理 degree_smul_of_smul_regular
  结论: {S : 类型} [SMulZero类 S R] {k : S}
  证明: by
  refine le_antisymm ?_ ?_
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    simp [hm m le_rfl]
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    refine h ?_
    simpa using hm m le_rfl

Depends on / 依赖: degree_le_iff_coeff_zero, degree_lt_iff_coeff_zero, le_antisymm, le_rfl
-/
theorem degree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).degree = p.degree := by
  refine le_antisymm ?_ ?_
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    simp [hm m le_rfl]
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    refine h ?_
    simpa using hm m le_rfl

/--
theorem `natDegree_smul_of_smul_regular` / 定理 `natDegree_smul_of_smul_regular`

English:
theorem natDegree_smul_of_smul_regular
  statement: {S : Type*} [SMulZeroClass S R] {k : S}
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  rw [← Nat.cast_inj (R := WithBot Nat)]; rw [← degree_eq_natDegree hp]; rw [← degree_eq_natDegree]; rw [degree_smul_of_smul_regular p h]
  contrapose hp
  rw [← smul_zero k] at hp
  exact h.polynomial hp

中文:
定理 natDegree_smul_of_smul_regular
  结论: {S : 类型} [SMulZero类 S R] {k : S}
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  rw [← Nat.cast_inj (R := WithBot Nat)]; rw [← degree_eq_natDegree hp]; rw [← degree_eq_natDegree]; rw [degree_smul_of_smul_regular p h]
  contrapose hp
  rw [← smul_zero k] at hp
  exact h.polynomial hp

Depends on / 依赖: Nat.cast_inj, WithBot, cast_inj, contrapose, degree_eq_natDegree, degree_smul_of_smul_regular, h.polynomial, polynomial, smul_zero
-/
theorem natDegree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [← Nat.cast_inj (R := WithBot Nat)]; rw [← degree_eq_natDegree hp]; rw [← degree_eq_natDegree]; rw [degree_smul_of_smul_regular p h]
  contrapose hp
  rw [← smul_zero k] at hp
  exact h.polynomial hp

/--
theorem `leadingCoeff_smul_of_smul_regular` / 定理 `leadingCoeff_smul_of_smul_regular`

English:
theorem leadingCoeff_smul_of_smul_regular
  statement: {S : Type*} [SMulZeroClass S R] {k : S}
  proof: by
  rw [Polynomial.leadingCoeff]; rw [Polynomial.leadingCoeff]; rw [coeff_smul]; rw [natDegree_smul_of_smul_regular p h]

中文:
定理 leadingCoeff_smul_of_smul_regular
  结论: {S : 类型} [SMulZero类 S R] {k : S}
  证明: by
  rw [Polynomial.leadingCoeff]; rw [Polynomial.leadingCoeff]; rw [coeff_smul]; rw [natDegree_smul_of_smul_regular p h]

Depends on / 依赖: Polynomial, Polynomial.leadingCoeff, coeff_smul, leadingCoeff, natDegree_smul_of_smul_regular
-/
theorem leadingCoeff_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).leadingCoeff = k • p.leadingCoeff := by
  rw [Polynomial.leadingCoeff]; rw [Polynomial.leadingCoeff]; rw [coeff_smul]; rw [natDegree_smul_of_smul_regular p h]

/--
theorem `monic_of_isUnit_leadingCoeff_inv_smul` / 定理 `monic_of_isUnit_leadingCoeff_inv_smul`

English:
theorem monic_of_isUnit_leadingCoeff_inv_smul
  given: (h : IsUnit p.leadingCoeff)
  proof: by
  rw [Monic.def]; rw [leadingCoeff_smul_of_smul_regular _ (isSMulRegular_of_group _)]; rw [Units.smul_def]
  simp

中文:
定理 monic_of_isUnit_leadingCoeff_inv_smul
  条件: (h : 是单位 p.leadingCoeff)
  证明: by
  rw [Monic.def]; rw [leadingCoeff_smul_of_smul_regular _ (isSMulRegular_of_group _)]; rw [Units.smul_def]
  simp

Depends on / 依赖: Monic.def, Units.smul_def, isSMulRegular_of_group, leadingCoeff_smul_of_smul_regular, smul_def
-/
theorem monic_of_isUnit_leadingCoeff_inv_smul (h : IsUnit p.leadingCoeff) :
    Monic (h.unit⁻¹ • p) := by
  rw [Monic.def]; rw [leadingCoeff_smul_of_smul_regular _ (isSMulRegular_of_group _)]; rw [Units.smul_def]
  simp

/--
theorem `isUnit_leadingCoeff_mul_right_eq_zero_iff` / 定理 `isUnit_leadingCoeff_mul_right_eq_zero_iff`

English:
theorem isUnit_leadingCoeff_mul_right_eq_zero_iff
  given: (h : IsUnit p.leadingCoeff) {q : R[X]}
  proof: by
  constructor
  · intro hp
    rw [← smul_eq_zero_iff_eq h.unit⁻¹] at hp
    have : h.unit⁻¹ • (p * q) = h.unit⁻¹ • p * q := by
      ext
      simp only [Units.smul_def, coeff_smul, coeff_mul, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [← mul_assoc]
    rwa [this, Monic.mul_right_eq_zero_iff] at hp
    exact monic_of_isUnit_leadingCoeff_inv_smul _
  · rintro rfl
    simp

中文:
定理 isUnit_leadingCoeff_mul_right_eq_zero_iff
  条件: (h : 是单位 p.leadingCoeff) {q : R[X]}
  证明: by
  constructor
  · intro hp
    rw [← smul_eq_zero_iff_eq h.unit⁻¹] at hp
    have : h.unit⁻¹ • (p * q) = h.unit⁻¹ • p * q := by
      ext
      simp only [Units.smul_def, coeff_smul, coeff_mul, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [← mul_assoc]
    rwa [this, Monic.mul_right_eq_zero_iff] at hp
    exact monic_of_isUnit_leadingCoeff_inv_smul _
  · rintro rfl
    simp

Depends on / 依赖: Monic.mul_right_eq_zero_iff, Units.smul_def, coeff_mul, coeff_smul, h.unit, monic_of_isUnit_leadingCoeff_inv_smul, mul_assoc, mul_right_eq_zero_iff, mul_sum, smul_def, smul_eq_mul, smul_eq_zero_iff_eq, sum_congr
-/
theorem isUnit_leadingCoeff_mul_right_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} :
    p * q = 0 ↔ q = 0 := by
  constructor
  · intro hp
    rw [← smul_eq_zero_iff_eq h.unit⁻¹] at hp
    have : h.unit⁻¹ • (p * q) = h.unit⁻¹ • p * q := by
      ext
      simp only [Units.smul_def, coeff_smul, coeff_mul, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [← mul_assoc]
    rwa [this, Monic.mul_right_eq_zero_iff] at hp
    exact monic_of_isUnit_leadingCoeff_inv_smul _
  · rintro rfl
    simp

/--
theorem `isUnit_leadingCoeff_mul_left_eq_zero_iff` / 定理 `isUnit_leadingCoeff_mul_left_eq_zero_iff`

English:
theorem isUnit_leadingCoeff_mul_left_eq_zero_iff
  given: (h : IsUnit p.leadingCoeff) {q : R[X]}
  proof: by
  constructor
  · intro hp
    replace hp := congr_arg (· * C ↑h.unit⁻¹) hp
    simp only [zero_mul] at hp
    rwa [mul_assoc, Monic.mul_left_eq_zero_iff] at hp
    refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    simp
  · rintro rfl
    rw [zero_mul]

中文:
定理 isUnit_leadingCoeff_mul_left_eq_zero_iff
  条件: (h : 是单位 p.leadingCoeff) {q : R[X]}
  证明: by
  constructor
  · intro hp
    replace hp := congr_arg (· * C ↑h.unit⁻¹) hp
    simp only [zero_mul] at hp
    rwa [mul_assoc, Monic.mul_left_eq_zero_iff] at hp
    refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    simp
  · rintro rfl
    rw [zero_mul]

Depends on / 依赖: Monic.mul_left_eq_zero_iff, congr_arg, h.unit, monic_mul_C_of_leadingCoeff_mul_eq_one, mul_assoc, mul_left_eq_zero_iff, replace, zero_mul
-/
theorem isUnit_leadingCoeff_mul_left_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} :
    q * p = 0 ↔ q = 0 := by
  constructor
  · intro hp
    replace hp := congr_arg (· * C ↑h.unit⁻¹) hp
    simp only [zero_mul] at hp
    rwa [mul_assoc, Monic.mul_left_eq_zero_iff] at hp
    refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    simp
  · rintro rfl
    rw [zero_mul]

end NotZeroDivisor

end Polynomial
