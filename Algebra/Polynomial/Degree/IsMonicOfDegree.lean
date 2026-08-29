/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Monic polynomials of given degree

This file defines the predicate `Polynomial.IsMonicOfDegree p n` that states that
the polynomial `p` is monic and has degree `n` (i.e., `p.natDegree = n`.)

We also provide some basic API.
-/

public section

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- This says that `p` has `natDegree` `n` and is monic. -/
@[mk_iff isMonicOfDegree_iff']
/--
Definition of `IsMonicOfDegree` / `IsMonicOfDegree` 的定义

English:
structure IsMonicOfDegree
  parameters: (p : R[X]) (n : Nat)
  axioms and operations (2):
    - natDegree_eq : p.natDegree = n
    - monic : p.Monic

中文:
结构 IsMonicOfDegree
  参数: (p : R[X]) (n : 自然数)
  公理与运算 (2 个):
    - natDegree_eq : p.natDegree = n
    - monic : p.Monic
-/
structure IsMonicOfDegree (p : R[X]) (n : Nat) : Prop where
  natDegree_eq : p.natDegree = n
  monic : p.Monic

@[simp]
/--
lemma `isMonicOfDegree_zero_iff` / 引理 `isMonicOfDegree_zero_iff`

English:
lemma isMonicOfDegree_zero_iff
  given: {p : R[X]}
  statement: IsMonicOfDegree p 0 ↔ p = 1
  proof: by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ => eq_one_of_monic_natDegree_zero H₂ H₁, fun H => ?_⟩
  subst H
  simp

中文:
引理 isMonicOfDegree_zero_iff
  条件: {p : R[X]}
  结论: IsMonicOfDegree p 0 ↔ p = 1
  证明: by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ => eq_one_of_monic_natDegree_zero H₂ H₁, fun H => ?_⟩
  subst H
  simp

Depends on / 依赖: eq_one_of_monic_natDegree_zero, isMonicOfDegree_iff
-/
lemma isMonicOfDegree_zero_iff {p : R[X]} : IsMonicOfDegree p 0 ↔ p = 1 := by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ => eq_one_of_monic_natDegree_zero H₂ H₁, fun H => ?_⟩
  subst H
  simp

/--
lemma `IsMonicOfDegree.leadingCoeff_eq` / 引理 `IsMonicOfDegree.leadingCoeff_eq`

English:
lemma IsMonicOfDegree.leadingCoeff_eq
  given: {p : R[X]} {n : Nat} (hp : IsMonicOfDegree p n)
  proof: Monic.def.mp hp.monic

@[simp]

中文:
引理 IsMonicOfDegree.leadingCoeff_eq
  条件: {p : R[X]} {n : 自然数} (hp : IsMonicOfDegree p n)
  证明: Monic.def.mp hp.monic

@[simp]

Depends on / 依赖: Monic.def.mp, hp.monic
-/
lemma IsMonicOfDegree.leadingCoeff_eq {p : R[X]} {n : Nat} (hp : IsMonicOfDegree p n) :
    p.leadingCoeff = 1 :=
  Monic.def.mp hp.monic

@[simp]
/--
lemma `isMonicOfDegree_iff_of_subsingleton` / 引理 `isMonicOfDegree_iff_of_subsingleton`

English:
lemma isMonicOfDegree_iff_of_subsingleton
  given: [Subsingleton R] {p : R[X]} {n : Nat}
  proof: by
  rw [Subsingleton.eq_one p]
  refine ⟨fun ⟨H, _⟩ => ?_, fun H => ?_⟩
  · rwa [natDegree_one, eq_comm] at H
  · rw [H, isMonicOfDegree_zero_iff]

中文:
引理 isMonicOfDegree_iff_of_subsingleton
  条件: [Subsingleton R] {p : R[X]} {n : 自然数}
  证明: by
  rw [Subsingleton.eq_one p]
  refine ⟨fun ⟨H, _⟩ => ?_, fun H => ?_⟩
  · rwa [natDegree_one, eq_comm] at H
  · rw [H, isMonicOfDegree_zero_iff]

Depends on / 依赖: Subsingleton, Subsingleton.eq_one, eq_comm, eq_one, isMonicOfDegree_zero_iff, natDegree_one
-/
lemma isMonicOfDegree_iff_of_subsingleton [Subsingleton R] {p : R[X]} {n : Nat} :
    IsMonicOfDegree p n ↔ n = 0 := by
  rw [Subsingleton.eq_one p]
  refine ⟨fun ⟨H, _⟩ => ?_, fun H => ?_⟩
  · rwa [natDegree_one, eq_comm] at H
  · rw [H, isMonicOfDegree_zero_iff]

/--
lemma `isMonicOfDegree_iff` / 引理 `isMonicOfDegree_iff`

English:
lemma isMonicOfDegree_iff
  given: [Nontrivial R] (p : R[X]) (n : Nat)
  proof: by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ => ⟨H₁.le, H₁ ▸ Monic.coeff_natDegree H₂⟩, fun ⟨H₁, H₂⟩ => ⟨?_, ?_⟩⟩
· exact natDegree_eq_of_le_of_coeff_ne_zero H₁ H₂ ▸ one_ne_zero
  · exact monic_of_natDegree_le_of_coeff_eq_one n H₁ H₂

中文:
引理 isMonicOfDegree_iff
  条件: [Nontrivial R] (p : R[X]) (n : 自然数)
  证明: by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ => ⟨H₁.le, H₁ ▸ Monic.coeff_natDegree H₂⟩, fun ⟨H₁, H₂⟩ => ⟨?_, ?_⟩⟩
· exact natDegree_eq_of_le_of_coeff_ne_zero H₁ H₂ ▸ one_ne_zero
  · exact monic_of_natDegree_le_of_coeff_eq_one n H₁ H₂

Depends on / 依赖: Monic.coeff_natDegree, coeff_natDegree, isMonicOfDegree_iff, monic_of_natDegree_le_of_coeff_eq_one, natDegree_eq_of_le_of_coeff_ne_zero, one_ne_zero
-/
lemma isMonicOfDegree_iff [Nontrivial R] (p : R[X]) (n : Nat) :
    IsMonicOfDegree p n ↔ p.natDegree <= n ∧ p.coeff n = 1 := by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ => ⟨H₁.le, H₁ ▸ Monic.coeff_natDegree H₂⟩, fun ⟨H₁, H₂⟩ => ⟨?_, ?_⟩⟩
· exact natDegree_eq_of_le_of_coeff_ne_zero H₁ H₂ ▸ one_ne_zero
  · exact monic_of_natDegree_le_of_coeff_eq_one n H₁ H₂

/--
lemma `IsMonicOfDegree.exists_natDegree_lt` / 引理 `IsMonicOfDegree.exists_natDegree_lt`

English:
lemma IsMonicOfDegree.exists_natDegree_lt
  statement: {p : R[X]} {n : Nat} (hn : n != 0)
  proof: by
  refine ⟨p.eraseLead, ?_, ?_⟩
  · nth_rewrite 1 [← p.eraseLead_add_C_mul_X_pow]
    rw [add_comm]; rw [hp.natDegree_eq]; rw [hp.leadingCoeff_eq]; rw [map_one]; rw [one_mul]
  · refine p.eraseLead_natDegree_le.trans_lt ?_
    rw [hp.natDegree_eq]
    lia

中文:
引理 IsMonicOfDegree.exists_natDegree_lt
  结论: {p : R[X]} {n : 自然数} (hn : n != 0)
  证明: by
  refine ⟨p.eraseLead, ?_, ?_⟩
  · nth_rewrite 1 [← p.eraseLead_add_C_mul_X_pow]
    rw [add_comm]; rw [hp.natDegree_eq]; rw [hp.leadingCoeff_eq]; rw [map_one]; rw [one_mul]
  · refine p.eraseLead_natDegree_le.trans_lt ?_
    rw [hp.natDegree_eq]
    lia

Depends on / 依赖: add_comm, eraseLead, eraseLead_add_C_mul_X_pow, eraseLead_natDegree_le, hp.leadingCoeff_eq, hp.natDegree_eq, leadingCoeff_eq, map_one, natDegree_eq, nth_rewrite, one_mul, p.eraseLead, p.eraseLead_add_C_mul_X_pow, p.eraseLead_natDegree_le.trans_lt, trans_lt
-/
lemma IsMonicOfDegree.exists_natDegree_lt {p : R[X]} {n : Nat} (hn : n != 0)
    (hp : IsMonicOfDegree p n) :
    exists q : R[X], p = X ^ n + q ∧ q.natDegree < n := by
  refine ⟨p.eraseLead, ?_, ?_⟩
  · nth_rewrite 1 [← p.eraseLead_add_C_mul_X_pow]
    rw [add_comm]; rw [hp.natDegree_eq]; rw [hp.leadingCoeff_eq]; rw [map_one]; rw [one_mul]
  · refine p.eraseLead_natDegree_le.trans_lt ?_
    rw [hp.natDegree_eq]
    lia

/--
lemma `IsMonicOfDegree.mul` / 引理 `IsMonicOfDegree.mul`

English:
lemma IsMonicOfDegree.mul
  statement: {p q : R[X]} {m n : Nat} (hp : IsMonicOfDegree p m)
  proof: by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hp hq ⊢
    exact ⟨hp, hq⟩
  refine ⟨?_, hp.monic.mul hq.monic⟩
  have : p.leadingCoeff * q.leadingCoeff != 0 := by
    rw [hp.leadingCoeff_eq]; rw [hq.leadingCoeff_eq]; rw

中文:
引理 IsMonicOfDegree.mul
  结论: {p q : R[X]} {m n : 自然数} (hp : IsMonicOfDegree p m)
  证明: by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hp hq ⊢
    exact ⟨hp, hq⟩
  refine ⟨?_, hp.monic.mul hq.monic⟩
  have : p.leadingCoeff * q.leadingCoeff != 0 := by
    rw [hp.leadingCoeff_eq]; rw [hq.leadingCoeff_eq]; rw

Depends on / 依赖: Nat.add_eq_zero_iff, add_eq_zero_iff, hp.leadingCoeff_eq, hp.monic.mul, hp.natDegree_eq, hq.leadingCoeff_eq, hq.monic, hq.natDegree_eq, isMonicOfDegree_iff_of_subsingleton, leadingCoeff, leadingCoeff_eq, natDegree_eq, natDegree_mul, one_mul, one_ne_zero, p.leadingCoeff, q.leadingCoeff, subsingleton_or_nontrivial
-/
lemma IsMonicOfDegree.mul {p q : R[X]} {m n : Nat} (hp : IsMonicOfDegree p m)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p * q) (m + n) := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hp hq ⊢
    exact ⟨hp, hq⟩
  refine ⟨?_, hp.monic.mul hq.monic⟩
  have : p.leadingCoeff * q.leadingCoeff != 0 := by
    rw [hp.leadingCoeff_eq]; rw [hq.leadingCoeff_eq]; rw [one_mul]
    exact one_ne_zero
  rw [natDegree_mul' this]; rw [hp.natDegree_eq]; rw [hq.natDegree_eq]

/--
lemma `IsMonicOfDegree.pow` / 引理 `IsMonicOfDegree.pow`

English:
lemma IsMonicOfDegree.pow
  given: {p : R[X]} {m : Nat} (hp : IsMonicOfDegree p m) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; rw [mul_add]; rw [mul_one]
    exact ih.mul hp

中文:
引理 IsMonicOfDegree.pow
  条件: {p : R[X]} {m : 自然数} (hp : IsMonicOfDegree p m) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; rw [mul_add]; rw [mul_one]
    exact ih.mul hp

Depends on / 依赖: ih.mul, mul_add, mul_one, pow_succ
-/
lemma IsMonicOfDegree.pow {p : R[X]} {m : Nat} (hp : IsMonicOfDegree p m) (n : Nat) :
    IsMonicOfDegree (p ^ n) (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; rw [mul_add]; rw [mul_one]
    exact ih.mul hp

/--
lemma `IsMonicOfDegree.coeff_eq` / 引理 `IsMonicOfDegree.coeff_eq`

English:
lemma IsMonicOfDegree.coeff_eq
  statement: {p q : R[X]} {n : Nat} (hp : IsMonicOfDegree p n)
  proof: by
  nontriviality R
  rw [isMonicOfDegree_iff] at hp hq
  rcases eq_or_lt_of_le hm with rfl | hm
  · rw [hp.2, hq.2]
  · replace hp : p.natDegree < m := hp.1.trans_lt hm
    replace hq : q.natDegree < m := hq.1.trans_lt hm
    rw [coeff_eq_zero_of_natDegree_lt hp]; rw [coeff_eq_zero_of_natDegree_lt

中文:
引理 IsMonicOfDegree.coeff_eq
  结论: {p q : R[X]} {n : 自然数} (hp : IsMonicOfDegree p n)
  证明: by
  nontriviality R
  rw [isMonicOfDegree_iff] at hp hq
  rcases eq_or_lt_of_le hm with rfl | hm
  · rw [hp.2, hq.2]
  · replace hp : p.natDegree < m := hp.1.trans_lt hm
    replace hq : q.natDegree < m := hq.1.trans_lt hm
    rw [coeff_eq_zero_of_natDegree_lt hp]; rw [coeff_eq_zero_of_natDegree_lt

Depends on / 依赖: coeff_eq_zero_of_natDegree_lt, eq_or_lt_of_le, isMonicOfDegree_iff, natDegree, nontriviality, p.natDegree, q.natDegree, replace, trans_lt
-/
lemma IsMonicOfDegree.coeff_eq {p q : R[X]} {n : Nat} (hp : IsMonicOfDegree p n)
    (hq : IsMonicOfDegree q n) {m : Nat} (hm : n <= m) :
    p.coeff m = q.coeff m := by
  nontriviality R
  rw [isMonicOfDegree_iff] at hp hq
  rcases eq_or_lt_of_le hm with rfl | hm
  · rw [hp.2, hq.2]
  · replace hp : p.natDegree < m := hp.1.trans_lt hm
    replace hq : q.natDegree < m := hq.1.trans_lt hm
    rw [coeff_eq_zero_of_natDegree_lt hp]; rw [coeff_eq_zero_of_natDegree_lt hq]

/--
lemma `IsMonicOfDegree.of_mul_left` / 引理 `IsMonicOfDegree.of_mul_left`

English:
lemma IsMonicOfDegree.of_mul_left
  statement: {p q : R[X]} {m n : Nat} (hp : IsMonicOfDegree p m)
  proof: by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.2
  have h₂ : q.Monic := hp.monic.of_mul_monic_left hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff !=

中文:
引理 IsMonicOfDegree.of_mul_left
  结论: {p q : R[X]} {m n : 自然数} (hp : IsMonicOfDegree p m)
  证明: by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.2
  have h₂ : q.Monic := hp.monic.of_mul_monic_left hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff !=

Depends on / 依赖: Nat.add_eq_zero_iff, Nat.add_left_cancel, add_eq_zero_iff, add_left_cancel, hp.leadingCoeff_eq, hp.monic.of_mul_monic_left, hp.natDegree_eq, hpq.monic, hpq.natDegree_eq, isMonicOfDegree_iff_of_subsingleton, leadingCoeff, leadingCoeff_eq, natDegree_eq, natDegree_mul, of_mul_monic_left, one_mul, one_ne_zero, p.leadingCoeff, q.Monic, q.leadingCoeff
-/
lemma IsMonicOfDegree.of_mul_left {p q : R[X]} {m n : Nat} (hp : IsMonicOfDegree p m)
    (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree q n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.2
  have h₂ : q.Monic := hp.monic.of_mul_monic_left hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff != 0 := by
    rw [hp.leadingCoeff_eq]; rw [h₂.leadingCoeff]; rw [one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h]; rw [hp.natDegree_eq] at this
  exact (Nat.add_left_cancel this.symm).symm

/--
lemma `IsMonicOfDegree.of_mul_right` / 引理 `IsMonicOfDegree.of_mul_right`

English:
lemma IsMonicOfDegree.of_mul_right
  statement: {p q : R[X]} {m n : Nat} (hq : IsMonicOfDegree q n)
  proof: by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.1
  have h₂ : p.Monic := hq.monic.of_mul_monic_right hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff !

中文:
引理 IsMonicOfDegree.of_mul_right
  结论: {p q : R[X]} {m n : 自然数} (hq : IsMonicOfDegree q n)
  证明: by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.1
  have h₂ : p.Monic := hq.monic.of_mul_monic_right hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff !

Depends on / 依赖: Nat.add_eq_zero_iff, Nat.add_right_cancel, add_eq_zero_iff, add_right_cancel, hpq.monic, hpq.natDegree_eq, hq.leadingCoeff_eq, hq.monic.of_mul_monic_right, hq.natDegree_eq, isMonicOfDegree_iff_of_subsingleton, leadingCoeff, leadingCoeff_eq, natDegree_eq, natDegree_mul, of_mul_monic_right, one_mul, one_ne_zero, p.Monic, p.leadingCoeff, q.leadingCoeff
-/
lemma IsMonicOfDegree.of_mul_right {p q : R[X]} {m n : Nat} (hq : IsMonicOfDegree q n)
    (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree p m := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.1
  have h₂ : p.Monic := hq.monic.of_mul_monic_right hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff != 0 := by
    rw [h₂.leadingCoeff]; rw [hq.leadingCoeff_eq]; rw [one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h]; rw [hq.natDegree_eq] at this
  exact (Nat.add_right_cancel this.symm).symm

/--
lemma `IsMonicOfDegree.add_right` / 引理 `IsMonicOfDegree.add_right`

English:
lemma IsMonicOfDegree.add_right
  statement: {p q : R[X]} {n : Nat} (hp : IsMonicOfDegree p n)
  proof: by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  refine (isMonicOfDegree_iff ..).mpr ⟨?_, ?_⟩
  · exact natDegree_add_le_of_degree_le hp.natDegree_eq.le hq.le
  · rw [coeff_add_eq_left_of_lt hq]
    exact ((isMonicOfDegree_iff p n).mp hp).2

中文:
引理 IsMonicOfDegree.add_right
  结论: {p q : R[X]} {n : 自然数} (hp : IsMonicOfDegree p n)
  证明: by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  refine (isMonicOfDegree_iff ..).mpr ⟨?_, ?_⟩
  · exact natDegree_add_le_of_degree_le hp.natDegree_eq.le hq.le
  · rw [coeff_add_eq_left_of_lt hq]
    exact ((isMonicOfDegree_iff p n).mp hp).2

Depends on / 依赖: coeff_add_eq_left_of_lt, hp.natDegree_eq.le, hq.le, isMonicOfDegree_iff, natDegree_add_le_of_degree_le, natDegree_eq, subsingleton_or_nontrivial
-/
lemma IsMonicOfDegree.add_right {p q : R[X]} {n : Nat} (hp : IsMonicOfDegree p n)
    (hq : q.natDegree < n) :
    IsMonicOfDegree (p + q) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  refine (isMonicOfDegree_iff ..).mpr ⟨?_, ?_⟩
  · exact natDegree_add_le_of_degree_le hp.natDegree_eq.le hq.le
  · rw [coeff_add_eq_left_of_lt hq]
    exact ((isMonicOfDegree_iff p n).mp hp).2

/--
lemma `IsMonicOfDegree.add_left` / 引理 `IsMonicOfDegree.add_left`

English:
lemma IsMonicOfDegree.add_left
  statement: {p q : R[X]} {n : Nat} (hp : p.natDegree < n)
  proof: by
  rw [add_comm]
  exact hq.add_right hp

中文:
引理 IsMonicOfDegree.add_left
  结论: {p q : R[X]} {n : 自然数} (hp : p.natDegree < n)
  证明: by
  rw [add_comm]
  exact hq.add_right hp

Depends on / 依赖: add_comm, add_right, hq.add_right
-/
lemma IsMonicOfDegree.add_left {p q : R[X]} {n : Nat} (hp : p.natDegree < n)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p + q) n := by
  rw [add_comm]
  exact hq.add_right hp

/--
lemma `IsMonicOfDegree.comp` / 引理 `IsMonicOfDegree.comp`

English:
lemma IsMonicOfDegree.comp
  statement: {p q : R[X]} {m n : Nat} (hn : n != 0) (hp : IsMonicOfDegree p m)
  proof: by
  rcases subsingleton_or_nontrivial R with h | h
  · simp only [isMonicOfDegree_iff_of_subsingleton, mul_eq_zero] at hp ⊢
    exact .inl hp
  rw [← hp.natDegree_eq]; rw [← hq.natDegree_eq]
  refine (isMonicOfDegree_iff ..).mpr ⟨natDegree_comp_le, ?_⟩
  rw [coeff_comp_degree_mul_degree (hq.natDegr

中文:
引理 IsMonicOfDegree.comp
  结论: {p q : R[X]} {m n : 自然数} (hn : n != 0) (hp : IsMonicOfDegree p m)
  证明: by
  rcases subsingleton_or_nontrivial R with h | h
  · simp only [isMonicOfDegree_iff_of_subsingleton, mul_eq_zero] at hp ⊢
    exact .inl hp
  rw [← hp.natDegree_eq]; rw [← hq.natDegree_eq]
  refine (isMonicOfDegree_iff ..).mpr ⟨natDegree_comp_le, ?_⟩
  rw [coeff_comp_degree_mul_degree (hq.natDegr

Depends on / 依赖: coeff_comp_degree_mul_degree, hp.leadingCoeff_eq, hp.natDegree_eq, hq.leadingCoeff_eq, hq.natDegree_eq, isMonicOfDegree_iff, isMonicOfDegree_iff_of_subsingleton, leadingCoeff_eq, mul_eq_zero, natDegree_comp_le, natDegree_eq, one_mul, one_pow, subsingleton_or_nontrivial
-/
lemma IsMonicOfDegree.comp {p q : R[X]} {m n : Nat} (hn : n != 0) (hp : IsMonicOfDegree p m)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p.comp q) (m * n) := by
  rcases subsingleton_or_nontrivial R with h | h
  · simp only [isMonicOfDegree_iff_of_subsingleton, mul_eq_zero] at hp ⊢
    exact .inl hp
  rw [← hp.natDegree_eq]; rw [← hq.natDegree_eq]
  refine (isMonicOfDegree_iff ..).mpr ⟨natDegree_comp_le, ?_⟩
  rw [coeff_comp_degree_mul_degree (hq.natDegree_eq ▸ hn)]; rw [hp.leadingCoeff_eq]; rw [hq.leadingCoeff_eq]; rw [one_pow]; rw [one_mul]

variable [Nontrivial R]

/--
lemma `IsMonicOfDegree.ne_zero` / 引理 `IsMonicOfDegree.ne_zero`

English:
lemma IsMonicOfDegree.ne_zero
  given: {p : R[X]} {n : Nat} (h : IsMonicOfDegree p n)
  statement: p != 0
  proof: h.monic.ne_zero

中文:
引理 IsMonicOfDegree.ne_zero
  条件: {p : R[X]} {n : 自然数} (h : IsMonicOfDegree p n)
  结论: p != 0
  证明: h.monic.ne_zero

Depends on / 依赖: h.monic.ne_zero, ne_zero
-/
lemma IsMonicOfDegree.ne_zero {p : R[X]} {n : Nat} (h : IsMonicOfDegree p n) : p != 0 :=
  h.monic.ne_zero

variable (R) in
/--
lemma `isMonicOfDegree_X` / 引理 `isMonicOfDegree_X`

English:
lemma isMonicOfDegree_X
  statement: IsMonicOfDegree (X : R[X]) 1
  proof: (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_le, coeff_X_one⟩

中文:
引理 isMonicOfDegree_X
  结论: IsMonicOfDegree (X : R[X]) 1
  证明: (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_le, coeff_X_one⟩

Depends on / 依赖: coeff_X_one, isMonicOfDegree_iff, natDegree_X_le
-/
lemma isMonicOfDegree_X : IsMonicOfDegree (X : R[X]) 1 :=
  (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_le, coeff_X_one⟩

variable (R) in
/--
lemma `isMonicOfDegree_X_pow` / 引理 `isMonicOfDegree_X_pow`

English:
lemma isMonicOfDegree_X_pow
  given: (n : Nat)
  statement: IsMonicOfDegree ((X : R[X]) ^ n) n
  proof: (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_pow_le n, coeff_X_pow_self n⟩

中文:
引理 isMonicOfDegree_X_pow
  条件: (n : 自然数)
  结论: IsMonicOfDegree ((X : R[X]) ^ n) n
  证明: (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_pow_le n, coeff_X_pow_self n⟩

Depends on / 依赖: coeff_X_pow_self, isMonicOfDegree_iff, natDegree_X_pow_le
-/
lemma isMonicOfDegree_X_pow (n : Nat) : IsMonicOfDegree ((X : R[X]) ^ n) n :=
  (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_pow_le n, coeff_X_pow_self n⟩

/--
lemma `isMonicOfDegree_monomial_one` / 引理 `isMonicOfDegree_monomial_one`

English:
lemma isMonicOfDegree_monomial_one
  given: (n : Nat)
  statement: IsMonicOfDegree (monomial n (1 : R)) n
  proof: by
  simpa only [monomial_one_right_eq_X_pow] using isMonicOfDegree_X_pow R n

中文:
引理 isMonicOfDegree_monomial_one
  条件: (n : 自然数)
  结论: IsMonicOfDegree (monomial n (1 : R)) n
  证明: by
  simpa only [monomial_one_right_eq_X_pow] using isMonicOfDegree_X_pow R n

Depends on / 依赖: isMonicOfDegree_X_pow, monomial_one_right_eq_X_pow, mul_right_cancel_of_ne_zero
-/
lemma isMonicOfDegree_monomial_one (n : Nat) : IsMonicOfDegree (monomial n (1 : R)) n := by
  simpa only [monomial_one_right_eq_X_pow] using isMonicOfDegree_X_pow R n

/--
lemma `isMonicOfDegree_X_add_one` / 引理 `isMonicOfDegree_X_add_one`

English:
lemma isMonicOfDegree_X_add_one
  given: (r : R)
  statement: IsMonicOfDegree (X + C r) 1
  proof: (isMonicOfDegree_X R).add_right (by rw [natDegree_C]; exact zero_lt_one)

中文:
引理 isMonicOfDegree_X_add_one
  条件: (r : R)
  结论: IsMonicOfDegree (X + C r) 1
  证明: (isMonicOfDegree_X R).add_right (by rw [natDegree_C]; exact zero_lt_one)

Depends on / 依赖: add_right, isMonicOfDegree_X, natDegree_C, zero_lt_one
-/
lemma isMonicOfDegree_X_add_one (r : R) : IsMonicOfDegree (X + C r) 1 :=
  (isMonicOfDegree_X R).add_right (by rw [natDegree_C]; exact zero_lt_one)

/--
lemma `isMonicOfDegree_one_iff` / 引理 `isMonicOfDegree_one_iff`

English:
lemma isMonicOfDegree_one_iff
  given: {f : R[X]}
  statement: IsMonicOfDegree f 1 ↔ exists r : R, f = X + C r
  proof: by
  refine ⟨fun H => ?_, fun ⟨r, H⟩ => H ▸ isMonicOfDegree_X_add_one r⟩
  refine ⟨f.coeff 0, ?_⟩
  ext1 n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact H.coeff_eq (isMonicOfDegree_X_add_one _) (by lia)

中文:
引理 isMonicOfDegree_one_iff
  条件: {f : R[X]}
  结论: IsMonicOfDegree f 1 ↔ 存在 r : R, f = X + C r
  证明: by
  refine ⟨fun H => ?_, fun ⟨r, H⟩ => H ▸ isMonicOfDegree_X_add_one r⟩
  refine ⟨f.coeff 0, ?_⟩
  ext1 n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact H.coeff_eq (isMonicOfDegree_X_add_one _) (by lia)

Depends on / 依赖: H.coeff_eq, coeff_eq, eq_zero_or_pos, f.coeff, isMonicOfDegree_X_add_one, n.eq_zero_or_pos
-/
lemma isMonicOfDegree_one_iff {f : R[X]} : IsMonicOfDegree f 1 ↔ exists r : R, f = X + C r := by
  refine ⟨fun H => ?_, fun ⟨r, H⟩ => H ▸ isMonicOfDegree_X_add_one r⟩
  refine ⟨f.coeff 0, ?_⟩
  ext1 n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact H.coeff_eq (isMonicOfDegree_X_add_one _) (by lia)

/--
lemma `isMonicOfDegree_add_add_two` / 引理 `isMonicOfDegree_add_add_two`

English:
lemma isMonicOfDegree_add_add_two
  given: (a b : R)
  statement: IsMonicOfDegree (X ^ 2 + C a * X + C b) 2
  proof: by
  rw [add_assoc]
exact (isMonicOfDegree_X_pow R 2).add_right
    calc
    _ <= max (C a * X).natDegree (C b).natDegree := natDegree_add_le ..
    _ = (C a * X).natDegree := by simp
.trans_lt one_lt_two .trans natDegree_X_le _ < 2 := natDegree_C_mul_le ..

中文:
引理 isMonicOfDegree_add_add_two
  条件: (a b : R)
  结论: IsMonicOfDegree (X ^ 2 + C a * X + C b) 2
  证明: by
  rw [add_assoc]
exact (isMonicOfDegree_X_pow R 2).add_right
    calc
    _ <= max (C a * X).natDegree (C b).natDegree := natDegree_add_le ..
    _ = (C a * X).natDegree := by simp
.trans_lt one_lt_two .trans natDegree_X_le _ < 2 := natDegree_C_mul_le ..

Depends on / 依赖: add_assoc, add_right, isMonicOfDegree_X_pow, natDegree, natDegree_C_mul_le, natDegree_X_le, natDegree_add_le, one_lt_two, trans_lt
-/
lemma isMonicOfDegree_add_add_two (a b : R) : IsMonicOfDegree (X ^ 2 + C a * X + C b) 2 := by
  rw [add_assoc]
exact (isMonicOfDegree_X_pow R 2).add_right
    calc
    _ <= max (C a * X).natDegree (C b).natDegree := natDegree_add_le ..
    _ = (C a * X).natDegree := by simp
.trans_lt one_lt_two .trans natDegree_X_le _ < 2 := natDegree_C_mul_le ..

/--
lemma `isMonicOfDegree_two_iff` / 引理 `isMonicOfDegree_two_iff`

English:
lemma isMonicOfDegree_two_iff
  given: {f : R[X]}
  proof: by
  refine ⟨fun H => ?_, fun ⟨a, b, h⟩ => h ▸ isMonicOfDegree_add_add_two a b⟩
  refine ⟨f.coeff 1, f.coeff 0, ext fun n => ?_⟩
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · obtain rfl : n = 0 := Nat.lt_one_iff.mp hn
    simp
  · simp
  · exact H.coeff_eq (isMonicOfDegree_add_add_two ..) (by li

中文:
引理 isMonicOfDegree_two_iff
  条件: {f : R[X]}
  证明: by
  refine ⟨fun H => ?_, fun ⟨a, b, h⟩ => h ▸ isMonicOfDegree_add_add_two a b⟩
  refine ⟨f.coeff 1, f.coeff 0, ext fun n => ?_⟩
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · obtain rfl : n = 0 := Nat.lt_one_iff.mp hn
    simp
  · simp
  · exact H.coeff_eq (isMonicOfDegree_add_add_two ..) (by li

Depends on / 依赖: H.coeff_eq, Nat.lt_one_iff.mp, coeff_eq, f.coeff, isMonicOfDegree_add_add_two, lt_one_iff, lt_trichotomy
-/
lemma isMonicOfDegree_two_iff {f : R[X]} :
    IsMonicOfDegree f 2 ↔ exists a b : R, f = X ^ 2 + C a * X + C b := by
  refine ⟨fun H => ?_, fun ⟨a, b, h⟩ => h ▸ isMonicOfDegree_add_add_two a b⟩
  refine ⟨f.coeff 1, f.coeff 0, ext fun n => ?_⟩
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · obtain rfl : n = 0 := Nat.lt_one_iff.mp hn
    simp
  · simp
  · exact H.coeff_eq (isMonicOfDegree_add_add_two ..) (by lia)

end Semiring

section Ring

variable [Ring R]

/--
lemma `IsMonicOfDegree.natDegree_sub_X_pow` / 引理 `IsMonicOfDegree.natDegree_sub_X_pow`

English:
lemma IsMonicOfDegree.natDegree_sub_X_pow
  statement: {p : R[X]} {n : Nat} (hn : n != 0)
  proof: by
  obtain ⟨q, hq₁, hq₂⟩ := hp.exists_natDegree_lt hn
  simpa [hq₁]

中文:
引理 IsMonicOfDegree.natDegree_sub_X_pow
  结论: {p : R[X]} {n : 自然数} (hn : n != 0)
  证明: by
  obtain ⟨q, hq₁, hq₂⟩ := hp.exists_natDegree_lt hn
  simpa [hq₁]

Depends on / 依赖: exists_natDegree_lt, hp.exists_natDegree_lt
-/
lemma IsMonicOfDegree.natDegree_sub_X_pow {p : R[X]} {n : Nat} (hn : n != 0)
    (hp : IsMonicOfDegree p n) :
    (p - X ^ n).natDegree < n := by
  obtain ⟨q, hq₁, hq₂⟩ := hp.exists_natDegree_lt hn
  simpa [hq₁]

/--
lemma `IsMonicOfDegree.natDegree_sub_lt` / 引理 `IsMonicOfDegree.natDegree_sub_lt`

English:
lemma IsMonicOfDegree.natDegree_sub_lt
  statement: {p q : R[X]} {n : Nat} (hn : n != 0) (hp : IsMonicOfDegree p n)
  proof: by
  rw [← sub_sub_sub_cancel_right p q (X ^ n)]
  replace hp := hp.natDegree_sub_X_pow hn
  replace hq := hq.natDegree_sub_X_pow hn
  rw [← Nat.le_sub_one_iff_lt (Nat.zero_lt_of_ne_zero hn)] at hp hq ⊢
  exact (natDegree_sub_le_iff_left hq).mpr hp

中文:
引理 IsMonicOfDegree.natDegree_sub_lt
  结论: {p q : R[X]} {n : 自然数} (hn : n != 0) (hp : IsMonicOfDegree p n)
  证明: by
  rw [← sub_sub_sub_cancel_right p q (X ^ n)]
  replace hp := hp.natDegree_sub_X_pow hn
  replace hq := hq.natDegree_sub_X_pow hn
  rw [← Nat.le_sub_one_iff_lt (Nat.zero_lt_of_ne_zero hn)] at hp hq ⊢
  exact (natDegree_sub_le_iff_left hq).mpr hp

Depends on / 依赖: Nat.le_sub_one_iff_lt, Nat.zero_lt_of_ne_zero, hp.natDegree_sub_X_pow, hq.natDegree_sub_X_pow, le_sub_one_iff_lt, natDegree_sub_X_pow, natDegree_sub_le_iff_left, replace, sub_sub_sub_cancel_right, zero_lt_of_ne_zero
-/
lemma IsMonicOfDegree.natDegree_sub_lt {p q : R[X]} {n : Nat} (hn : n != 0) (hp : IsMonicOfDegree p n)
    (hq : IsMonicOfDegree q n) :
    (p - q).natDegree < n := by
  rw [← sub_sub_sub_cancel_right p q (X ^ n)]
  replace hp := hp.natDegree_sub_X_pow hn
  replace hq := hq.natDegree_sub_X_pow hn
  rw [← Nat.le_sub_one_iff_lt (Nat.zero_lt_of_ne_zero hn)] at hp hq ⊢
  exact (natDegree_sub_le_iff_left hq).mpr hp

/--
lemma `IsMonicOfDegree.sub` / 引理 `IsMonicOfDegree.sub`

English:
lemma IsMonicOfDegree.sub
  given: {p q : R[X]} {n : Nat} (hp : IsMonicOfDegree p n) (hq : q.natDegree < n)
  proof: by
  rw [sub_eq_add_neg]
exact hp.add_right (natDegree_neg q) ▸ hq

中文:
引理 IsMonicOfDegree.sub
  条件: {p q : R[X]} {n : 自然数} (hp : IsMonicOfDegree p n) (hq : q.natDegree < n)
  证明: by
  rw [sub_eq_add_neg]
exact hp.add_right (natDegree_neg q) ▸ hq

Depends on / 依赖: add_right, hp.add_right, natDegree_neg, sub_eq_add_neg
-/
lemma IsMonicOfDegree.sub {p q : R[X]} {n : Nat} (hp : IsMonicOfDegree p n) (hq : q.natDegree < n) :
    IsMonicOfDegree (p - q) n := by
  rw [sub_eq_add_neg]
exact hp.add_right (natDegree_neg q) ▸ hq

variable [Nontrivial R]

/--
lemma `isMonicOfDegree_X_sub_one` / 引理 `isMonicOfDegree_X_sub_one`

English:
lemma isMonicOfDegree_X_sub_one
  given: (r : R)
  statement: IsMonicOfDegree (X - C r) 1
  proof: (isMonicOfDegree_X R).sub (by rw [natDegree_C]; exact zero_lt_one)

中文:
引理 isMonicOfDegree_X_sub_one
  条件: (r : R)
  结论: IsMonicOfDegree (X - C r) 1
  证明: (isMonicOfDegree_X R).sub (by rw [natDegree_C]; exact zero_lt_one)

Depends on / 依赖: isMonicOfDegree_X, natDegree_C, zero_lt_one
-/
lemma isMonicOfDegree_X_sub_one (r : R) : IsMonicOfDegree (X - C r) 1 :=
  (isMonicOfDegree_X R).sub (by rw [natDegree_C]; exact zero_lt_one)

/--
lemma `isMonicOfDegree_sub_add_two` / 引理 `isMonicOfDegree_sub_add_two`

English:
lemma isMonicOfDegree_sub_add_two
  given: (a b : R)
  statement: IsMonicOfDegree (X ^ 2 - C a * X + C b) 2
  proof: by
  rw [sub_add]
exact (isMonicOfDegree_X_pow R 2).add_right by
    rw [natDegree_neg]
    calc
    _ <= max (C a * X).natDegree (C b).natDegree := natDegree_sub_le ..
    _ = (C a * X).natDegree := by simp
.trans_lt one_lt_two .trans natDegree_X_le _ < 2 := natDegree_C_mul_le ..

中文:
引理 isMonicOfDegree_sub_add_two
  条件: (a b : R)
  结论: IsMonicOfDegree (X ^ 2 - C a * X + C b) 2
  证明: by
  rw [sub_add]
exact (isMonicOfDegree_X_pow R 2).add_right by
    rw [natDegree_neg]
    calc
    _ <= max (C a * X).natDegree (C b).natDegree := natDegree_sub_le ..
    _ = (C a * X).natDegree := by simp
.trans_lt one_lt_two .trans natDegree_X_le _ < 2 := natDegree_C_mul_le ..

Depends on / 依赖: add_right, isMonicOfDegree_X_pow, natDegree, natDegree_C_mul_le, natDegree_X_le, natDegree_neg, natDegree_sub_le, one_lt_two, sub_add, trans_lt
-/
lemma isMonicOfDegree_sub_add_two (a b : R) : IsMonicOfDegree (X ^ 2 - C a * X + C b) 2 := by
  rw [sub_add]
exact (isMonicOfDegree_X_pow R 2).add_right by
    rw [natDegree_neg]
    calc
    _ <= max (C a * X).natDegree (C b).natDegree := natDegree_sub_le ..
    _ = (C a * X).natDegree := by simp
.trans_lt one_lt_two .trans natDegree_X_le _ < 2 := natDegree_C_mul_le ..

/--
lemma `isMonicOfDegree_two_iff'` / 引理 `isMonicOfDegree_two_iff'`

English:
lemma isMonicOfDegree_two_iff'
  given: {f : R[X]}
  proof: by
  refine ⟨fun H => ?_, fun ⟨a, b, h⟩ => h ▸ isMonicOfDegree_sub_add_two a b⟩
  simp only [sub_eq_add_neg, ← neg_mul, ← map_neg]
  obtain ⟨a, b, h⟩ := isMonicOfDegree_two_iff.mp H
  exact ⟨-a, b, (neg_neg a).symm ▸ h⟩

中文:
引理 isMonicOfDegree_two_iff'
  条件: {f : R[X]}
  证明: by
  refine ⟨fun H => ?_, fun ⟨a, b, h⟩ => h ▸ isMonicOfDegree_sub_add_two a b⟩
  simp only [sub_eq_add_neg, ← neg_mul, ← map_neg]
  obtain ⟨a, b, h⟩ := isMonicOfDegree_two_iff.mp H
  exact ⟨-a, b, (neg_neg a).symm ▸ h⟩

Depends on / 依赖: isMonicOfDegree_sub_add_two, isMonicOfDegree_two_iff, isMonicOfDegree_two_iff.mp, map_neg, neg_mul, neg_neg, sub_eq_add_neg
-/
lemma isMonicOfDegree_two_iff' {f : R[X]} :
    IsMonicOfDegree f 2 ↔ exists a b : R, f = X ^ 2 - C a * X + C b := by
  refine ⟨fun H => ?_, fun ⟨a, b, h⟩ => h ▸ isMonicOfDegree_sub_add_two a b⟩
  simp only [sub_eq_add_neg, ← neg_mul, ← map_neg]
  obtain ⟨a, b, h⟩ := isMonicOfDegree_two_iff.mp H
  exact ⟨-a, b, (neg_neg a).symm ▸ h⟩

end Ring

section CommRing

variable [CommRing R]

/--
lemma `IsMonicOfDegree.of_dvd_add` / 引理 `IsMonicOfDegree.of_dvd_add`

English:
lemma IsMonicOfDegree.of_dvd_add
  statement: {a b r : R[X]} {m n : Nat} (hmn : n <= m) (ha : IsMonicOfDegree a m)
  proof: by
  obtain ⟨q, hq⟩ := exists_eq_mul_left_of_dvd h
  refine ⟨q, hb.of_mul_right ?_, eq_sub_iff_add_eq.mpr hq⟩
  rw [← hq]; rw [show m - n + n = m by lia]
  exact ha.add_right hr

中文:
引理 IsMonicOfDegree.of_dvd_add
  结论: {a b r : R[X]} {m n : 自然数} (hmn : n <= m) (ha : IsMonicOfDegree a m)
  证明: by
  obtain ⟨q, hq⟩ := exists_eq_mul_left_of_dvd h
  refine ⟨q, hb.of_mul_right ?_, eq_sub_iff_add_eq.mpr hq⟩
  rw [← hq]; rw [show m - n + n = m by lia]
  exact ha.add_right hr

Depends on / 依赖: add_right, eq_sub_iff_add_eq, eq_sub_iff_add_eq.mpr, exists_eq_mul_left_of_dvd, ha.add_right, hb.of_mul_right, of_mul_right
-/
lemma IsMonicOfDegree.of_dvd_add {a b r : R[X]} {m n : Nat} (hmn : n <= m) (ha : IsMonicOfDegree a m)
    (hb : IsMonicOfDegree b n) (hr : r.natDegree < m) (h : b ∣ a + r) :
    exists q : R[X], IsMonicOfDegree q (m - n) ∧ a = q * b - r := by
  obtain ⟨q, hq⟩ := exists_eq_mul_left_of_dvd h
  refine ⟨q, hb.of_mul_right ?_, eq_sub_iff_add_eq.mpr hq⟩
  rw [← hq]; rw [show m - n + n = m by lia]
  exact ha.add_right hr

/--
lemma `IsMonicOfDegree.of_dvd_sub` / 引理 `IsMonicOfDegree.of_dvd_sub`

English:
lemma IsMonicOfDegree.of_dvd_sub
  statement: {a b r : R[X]} {m n : Nat} (hmn : n <= m) (ha : IsMonicOfDegree a m)
  proof: by
  convert ha.of_dvd_add hmn hb ?_ h with q
  · rw [sub_neg_eq_add]
  · rwa [natDegree_neg]

中文:
引理 IsMonicOfDegree.of_dvd_sub
  结论: {a b r : R[X]} {m n : 自然数} (hmn : n <= m) (ha : IsMonicOfDegree a m)
  证明: by
  convert ha.of_dvd_add hmn hb ?_ h with q
  · rw [sub_neg_eq_add]
  · rwa [natDegree_neg]

Depends on / 依赖: convert, ha.of_dvd_add, natDegree_neg, of_dvd_add, sub_neg_eq_add
-/
lemma IsMonicOfDegree.of_dvd_sub {a b r : R[X]} {m n : Nat} (hmn : n <= m) (ha : IsMonicOfDegree a m)
    (hb : IsMonicOfDegree b n) (hr : r.natDegree < m) (h : b ∣ a - r) :
    exists q : R[X], IsMonicOfDegree q (m - n) ∧ a = q * b + r := by
  convert ha.of_dvd_add hmn hb ?_ h with q
  · rw [sub_neg_eq_add]
  · rwa [natDegree_neg]

/--
lemma `IsMonicOfDegree.aeval_add` / 引理 `IsMonicOfDegree.aeval_add`

English:
lemma IsMonicOfDegree.aeval_add
  given: {p : R[X]} {n : Nat} (hp : IsMonicOfDegree p n) (r : R)
  proof: by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  rw [← mul_one n]
  exact hp.comp one_ne_zero (isMonicOfDegree_X_add_one r)

中文:
引理 IsMonicOfDegree.aeval_add
  条件: {p : R[X]} {n : 自然数} (hp : IsMonicOfDegree p n) (r : R)
  证明: by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  rw [← mul_one n]
  exact hp.comp one_ne_zero (isMonicOfDegree_X_add_one r)

Depends on / 依赖: hp.comp, isMonicOfDegree_X_add_one, mul_one, one_ne_zero, subsingleton_or_nontrivial
-/
lemma IsMonicOfDegree.aeval_add {p : R[X]} {n : Nat} (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X + C r) p) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  rw [← mul_one n]
  exact hp.comp one_ne_zero (isMonicOfDegree_X_add_one r)

/--
lemma `IsMonicOfDegree.aeval_sub` / 引理 `IsMonicOfDegree.aeval_sub`

English:
lemma IsMonicOfDegree.aeval_sub
  given: {p : R[X]} {n : Nat} (hp : IsMonicOfDegree p n) (r : R)
  proof: by
  rw [sub_eq_add_neg]; rw [← map_neg]
  exact aeval_add hp (-r)

中文:
引理 IsMonicOfDegree.aeval_sub
  条件: {p : R[X]} {n : 自然数} (hp : IsMonicOfDegree p n) (r : R)
  证明: by
  rw [sub_eq_add_neg]; rw [← map_neg]
  exact aeval_add hp (-r)

Depends on / 依赖: aeval_add, map_neg, sub_eq_add_neg
-/
lemma IsMonicOfDegree.aeval_sub {p : R[X]} {n : Nat} (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X - C r) p) n := by
  rw [sub_eq_add_neg]; rw [← map_neg]
  exact aeval_add hp (-r)

end CommRing

end Polynomial
