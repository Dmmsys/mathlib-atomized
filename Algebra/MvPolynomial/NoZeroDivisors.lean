/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Bolton Bailey
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import Mathlib.Algebra.MvPolynomial.Division

/-!
# Multivariate polynomials over integral domains

This file proves results about multivariate polynomials
that hold when the coefficient (semi)ring has no zero divisors.

-/

public section

open Finset Equiv

variable {R : Type*}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : Nat} {n m : σ} {s : σ ->₀ Nat}

section CommSemiring

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

section NoZeroDivisors

variable [NoZeroDivisors R]

section DegreeOf

/--
lemma `degreeOf_mul_eq` / 引理 `degreeOf_mul_eq`

English:
lemma degreeOf_mul_eq
  given: (hp : p != 0) (hq : q != 0)
  proof: by
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul] <;> simpa [-renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]

中文:
引理 degreeOf_mul_eq
  条件: (hp : p != 0) (hq : q != 0)
  证明: by
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul] <;> simpa [-renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_eq_zero_iff, Polynomial, Polynomial.natDegree_mul, classical, degreeOf_eq_natDegree, map_eq_zero_iff, map_mul, natDegree_mul, renameEquiv_apply, simp_rw
-/
lemma degreeOf_mul_eq (hp : p != 0) (hq : q != 0) :
    degreeOf n (p * q) = degreeOf n p + degreeOf n q := by
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul] <;> simpa [-renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]

/--
lemma `degreeOf_prod_eq` / 引理 `degreeOf_prod_eq`

English:
lemma degreeOf_prod_eq
  statement: {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R)
  proof: by
  rcases subsingleton_or_nontrivial (MvPolynomial σ R) with nontrivial | nontrivial
  · simp [Subsingleton.eq_zero (α := MvPolynomial σ R)]
  · classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s a_not_mem ih =>
      simp only [mem_insert, ne_eq, forall_

中文:
引理 degreeOf_prod_eq
  结论: {ι : 类型} (s : 有限集 ι) (f : ι -> 多元多项式 σ R)
  证明: by
  rcases subsingleton_or_nontrivial (MvPolynomial σ R) with nontrivial | nontrivial
  · simp [Subsingleton.eq_zero (α := MvPolynomial σ R)]
  · classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s a_not_mem ih =>
      simp only [mem_insert, ne_eq, forall_

Depends on / 依赖: Finset, Finset.induction_on, MvPolynomial, Subsingleton, Subsingleton.eq_zero, a_not_mem, classical, degreeOf_mul_eq, eq_zero, forall_eq_or_imp, induction_on, insert, mem_insert, ne_eq, nontrivial, not_false_eq_true, prod_insert, prod_ne_zero_iff, subsingleton_or_nontrivial, sum_insert
-/
lemma degreeOf_prod_eq {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R)
    (h : forall i in s, f i != 0) :
    degreeOf n (∏ i in s, f i) = ∑ i in s, degreeOf n (f i) := by
  rcases subsingleton_or_nontrivial (MvPolynomial σ R) with nontrivial | nontrivial
  · simp [Subsingleton.eq_zero (α := MvPolynomial σ R)]
  · classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s a_not_mem ih =>
      simp only [mem_insert, ne_eq, forall_eq_or_imp] at h
      obtain ⟨ha, hs⟩ := h
      simp [a_not_mem, not_false_eq_true, prod_insert, sum_insert, degreeOf_mul_eq ha
        (by rw [prod_ne_zero_iff]; exact hs), ih hs]

/--
theorem `degreeOf_pow_eq` / 定理 `degreeOf_pow_eq`

English:
theorem degreeOf_pow_eq
  given: (i : σ) (p : MvPolynomial σ R) (n : Nat) (hp : p != 0)
  proof: by
  rw [pow_eq_prod_const]; rw [degreeOf_prod_eq (range n) (fun _ => p) (fun _ _ => hp)]
  simp

中文:
定理 degreeOf_pow_eq
  条件: (i : σ) (p : 多元多项式 σ R) (n : 自然数) (hp : p != 0)
  证明: by
  rw [pow_eq_prod_const]; rw [degreeOf_prod_eq (range n) (fun _ => p) (fun _ _ => hp)]
  simp

Depends on / 依赖: degreeOf_prod_eq, pow_eq_prod_const
-/
theorem degreeOf_pow_eq (i : σ) (p : MvPolynomial σ R) (n : Nat) (hp : p != 0) :
    degreeOf i (p ^ n) = n * degreeOf i p := by
  rw [pow_eq_prod_const]; rw [degreeOf_prod_eq (range n) (fun _ => p) (fun _ _ => hp)]
  simp

end DegreeOf

section Degrees

/--
lemma `degrees_mul_eq` / 引理 `degrees_mul_eq`

English:
lemma degrees_mul_eq
  given: (hp : p != 0) (hq : q != 0)
  proof: by
  classical
  ext s
  simp_rw [Multiset.count_add, ← degreeOf_def, degreeOf_mul_eq hp hq]

中文:
引理 degrees_mul_eq
  条件: (hp : p != 0) (hq : q != 0)
  证明: by
  classical
  ext s
  simp_rw [Multiset.count_add, ← degreeOf_def, degreeOf_mul_eq hp hq]

Depends on / 依赖: Multiset, Multiset.count_add, classical, count_add, degreeOf_def, degreeOf_mul_eq, simp_rw
-/
lemma degrees_mul_eq (hp : p != 0) (hq : q != 0) :
    degrees (p * q) = degrees p + degrees q := by
  classical
  ext s
  simp_rw [Multiset.count_add, ← degreeOf_def, degreeOf_mul_eq hp hq]

end Degrees

/--
theorem `totalDegree_mul_of_isDomain` / 定理 `totalDegree_mul_of_isDomain`

English:
theorem totalDegree_mul_of_isDomain
  statement: {f g : MvPolynomial σ R}
  proof: by
  cases exists_wellFoundedGT σ
  simp [← degree_degLexDegree, MonomialOrder.degree_mul hf hg]

中文:
定理 totalDegree_mul_of_isDomain
  结论: {f g : 多元多项式 σ R}
  证明: by
  cases exists_wellFoundedGT σ
  simp [← degree_degLexDegree, MonomialOrder.degree_mul hf hg]

Depends on / 依赖: MonomialOrder, MonomialOrder.degree_mul, degree_degLexDegree, degree_mul, exists_wellFoundedGT
-/
theorem totalDegree_mul_of_isDomain {f g : MvPolynomial σ R}
    (hf : f != 0) (hg : g != 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  cases exists_wellFoundedGT σ
  simp [← degree_degLexDegree, MonomialOrder.degree_mul hf hg]

/--
theorem `totalDegree_le_of_dvd_of_isDomain` / 定理 `totalDegree_le_of_dvd_of_isDomain`

English:
theorem totalDegree_le_of_dvd_of_isDomain
  statement: {f g : MvPolynomial σ R}
  proof: by
  obtain ⟨r, rfl⟩ := h
  rw [totalDegree_mul_of_isDomain (by aesop) (by aesop)]
  lia

中文:
定理 totalDegree_le_of_dvd_of_isDomain
  结论: {f g : 多元多项式 σ R}
  证明: by
  obtain ⟨r, rfl⟩ := h
  rw [totalDegree_mul_of_isDomain (by aesop) (by aesop)]
  lia

Depends on / 依赖: totalDegree_mul_of_isDomain
-/
theorem totalDegree_le_of_dvd_of_isDomain {f g : MvPolynomial σ R}
    (h : f ∣ g) (hg : g != 0) :
    f.totalDegree <= g.totalDegree := by
  obtain ⟨r, rfl⟩ := h
  rw [totalDegree_mul_of_isDomain (by aesop) (by aesop)]
  lia

/--
theorem `dvd_C_iff_exists` / 定理 `dvd_C_iff_exists`

English:
theorem dvd_C_iff_exists
  given: {f : MvPolynomial σ R} {a : R} (ha : a != 0)
  proof: by
  constructor
  · intro hf
    use coeff 0 f
    suffices f.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      refine ⟨?_, this⟩
      rw [this]; rw [C_dvd_iff_dvd_coeff] at hf
      simpa using hf 0
    apply Nat.eq_zero_of_le_zero
    simpa using totalDegree_le_of_dvd_of_i

中文:
定理 dvd_C_iff_存在
  条件: {f : 多元多项式 σ R} {a : R} (ha : a != 0)
  证明: by
  constructor
  · intro hf
    use coeff 0 f
    suffices f.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      refine ⟨?_, this⟩
      rw [this]; rw [C_dvd_iff_dvd_coeff] at hf
      simpa using hf 0
    apply Nat.eq_zero_of_le_zero
    simpa using totalDegree_le_of_dvd_of_i

Depends on / 依赖: C_dvd_iff_dvd_coeff, Nat.eq_zero_of_le_zero, eq_zero_of_le_zero, f.totalDegree, map_dvd, totalDegree, totalDegree_eq_zero_iff_eq_C, totalDegree_le_of_dvd_of_isDomain
-/
theorem dvd_C_iff_exists {f : MvPolynomial σ R} {a : R} (ha : a != 0) :
    f ∣ C a ↔ exists b, b ∣ a ∧ f = C b := by
  constructor
  · intro hf
    use coeff 0 f
    suffices f.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      refine ⟨?_, this⟩
      rw [this]; rw [C_dvd_iff_dvd_coeff] at hf
      simpa using hf 0
    apply Nat.eq_zero_of_le_zero
    simpa using totalDegree_le_of_dvd_of_isDomain hf (by simp [ha])
  · rintro ⟨b, hab, rfl⟩
    exact map_dvd C hab

end NoZeroDivisors

section nonZeroDivisors

open nonZeroDivisors

/--
theorem `degreeOf_C_mul` / 定理 `degreeOf_C_mul`

English:
theorem degreeOf_C_mul
  given: (j : σ) (c : R) (hc : c in R⁰)
  statement: degreeOf j (C c * p) = degreeOf j p
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul']
  · simp
  · have hp' : (optionEquivLeft R _ ((rename (optionSubtypeNe j).symm) p)).leadingCoeff != 0 := by
      intro h
      exact hp (rename_injecti

中文:
定理 degreeOf_C_mul
  条件: (j : σ) (c : R) (hc : c in R⁰)
  结论: degreeOf j (C c * p) = degreeOf j p
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul']
  · simp
  · have hp' : (optionEquivLeft R _ ((rename (optionSubtypeNe j).symm) p)).leadingCoeff != 0 := by
      intro h
      exact hp (rename_injecti

Depends on / 依赖: Equiv.injective, Polynomial, Polynomial.leadingCoeff_C, Polynomial.natDegree_mul, algHom_C, algebraMap_eq, classical, congr_arg, contrapose, degreeOf_eq_natDegree, injective, leadingCoeff, leadingCoeff_C, map_mul, natDegree_mul, ne_eq, optionEquivLeft, optionEquivLeft_C, optionSubtypeNe, renameEquiv_apply
-/
theorem degreeOf_C_mul (j : σ) (c : R) (hc : c in R⁰) : degreeOf j (C c * p) = degreeOf j p := by
  by_cases hp : p = 0
  · simp [hp]
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul']
  · simp
  · have hp' : (optionEquivLeft R _ ((rename (optionSubtypeNe j).symm) p)).leadingCoeff != 0 := by
      intro h
      exact hp (rename_injective _ (Equiv.injective _) (by simpa using h))
    simp_rw [ne_eq, renameEquiv_apply, algHom_C, algebraMap_eq, optionEquivLeft_C,
      Polynomial.leadingCoeff_C]
    contrapose hp'
    ext m
    apply hc.1
    simpa using congr_arg (coeff m) hp'

end nonZeroDivisors

end CommSemiring

section CommRing

variable [CommRing R] [NoZeroDivisors R] {p q r : MvPolynomial σ R}

/--
theorem `dvd_monomial_iff_exists` / 定理 `dvd_monomial_iff_exists`

English:
theorem dvd_monomial_iff_exists
  given: {n : σ ->₀ Nat} {a : R} (ha : a != 0)
  proof: by
  rw [show monomial n a = monomial n 1 * C a by rw [mul_comm]; rw [C_mul_monomial]; rw [mul_one],
    dvd_monomial_mul_iff_exists]
  apply exists_congr
  intro m
  constructor
  · rintro ⟨r, hmn, hr, h⟩
    rw [dvd_C_iff_exists ha] at hr
    obtain ⟨b, hb, hr⟩ := hr
    use b, hmn, hb
    rw [h];

中文:
定理 dvd_monomial_iff_存在
  条件: {n : σ ->₀ 自然数} {a : R} (ha : a != 0)
  证明: by
  rw [show monomial n a = monomial n 1 * C a by rw [mul_comm]; rw [C_mul_monomial]; rw [mul_one],
    dvd_monomial_mul_iff_exists]
  apply exists_congr
  intro m
  constructor
  · rintro ⟨r, hmn, hr, h⟩
    rw [dvd_C_iff_exists ha] at hr
    obtain ⟨b, hb, hr⟩ := hr
    use b, hmn, hb
    rw [h];

Depends on / 依赖: C_mul_monomial, dvd_C_iff_exists, dvd_monomial_mul_iff_exists, exists_congr, map_dvd, monomial, mul_comm, mul_one
-/
theorem dvd_monomial_iff_exists {n : σ ->₀ Nat} {a : R} (ha : a != 0) :
    p ∣ monomial n a ↔ exists m b, m <= n ∧ b ∣ a ∧ p = monomial m b := by
  rw [show monomial n a = monomial n 1 * C a by rw [mul_comm]; rw [C_mul_monomial]; rw [mul_one],
    dvd_monomial_mul_iff_exists]
  apply exists_congr
  intro m
  constructor
  · rintro ⟨r, hmn, hr, h⟩
    rw [dvd_C_iff_exists ha] at hr
    obtain ⟨b, hb, hr⟩ := hr
    use b, hmn, hb
    rw [h]; rw [mul_comm]; rw [hr]; rw [C_mul_monomial]; rw [mul_one]
  · rintro ⟨b, hmn, hb, h⟩
    use C b, hmn, map_dvd C hb
    rwa [mul_comm, C_mul_monomial, mul_one]

/--
theorem `dvd_monomial_one_iff_exists` / 定理 `dvd_monomial_one_iff_exists`

English:
theorem dvd_monomial_one_iff_exists
  given: {n : σ ->₀ Nat}
  proof: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · suffices exists m, m <= n by simpa [Subsingleton.elim _ p]
    use n
  rw [dvd_monomial_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro m
  simp_rw [isUnit_iff_dvd_one]

中文:
定理 dvd_monomial_one_iff_存在
  条件: {n : σ ->₀ 自然数}
  证明: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · suffices exists m, m <= n by simpa [Subsingleton.elim _ p]
    use n
  rw [dvd_monomial_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro m
  simp_rw [isUnit_iff_dvd_one]

Depends on / 依赖: Subsingleton, Subsingleton.elim, dvd_monomial_iff_exists, exists_congr, isUnit_iff_dvd_one, one_ne_zero, simp_rw, subsingleton_or_nontrivial
-/
theorem dvd_monomial_one_iff_exists {n : σ ->₀ Nat} :
    p ∣ monomial n 1 ↔ exists m u, m <= n ∧ IsUnit u ∧ p = monomial m u := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · suffices exists m, m <= n by simpa [Subsingleton.elim _ p]
    use n
  rw [dvd_monomial_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro m
  simp_rw [isUnit_iff_dvd_one]

/--
theorem `dvd_smul_X_iff_exists` / 定理 `dvd_smul_X_iff_exists`

English:
theorem dvd_smul_X_iff_exists
  given: {i : σ} {r : R} (hr : r != 0)
  proof: by
  rw [X]; rw [smul_monomial]; rw [smul_eq_mul]; rw [mul_one]; rw [dvd_monomial_iff_exists hr]; rw [exists_comm]
  apply exists_congr
  intro b
  constructor
  · rintro ⟨m, hmn, hb, rfl⟩
    simp only [hb, true_and]
    suffices m = 0 ∨ m = Finsupp.single i 1 by
      apply this.imp <;> simp +cont

中文:
定理 dvd_smul_X_iff_存在
  条件: {i : σ} {r : R} (hr : r != 0)
  证明: by
  rw [X]; rw [smul_monomial]; rw [smul_eq_mul]; rw [mul_one]; rw [dvd_monomial_iff_exists hr]; rw [exists_comm]
  apply exists_congr
  intro b
  constructor
  · rintro ⟨m, hmn, hb, rfl⟩
    simp only [hb, true_and]
    suffices m = 0 ∨ m = Finsupp.single i 1 by
      apply this.imp <;> simp +cont

Depends on / 依赖: Finsupp, Finsupp.coe_zero, Finsupp.single, Finsupp.single_eq_of_ne, Nat.le_zero, Pi.zero_apply, coe_zero, contextual, dvd_monomial_iff_exists, exists_comm, exists_congr, le_zero, mul_one, single, single_eq_of_ne, smul_eq_mul, smul_monomial, this.imp, true_and, zero_apply
-/
theorem dvd_smul_X_iff_exists {i : σ} {r : R} (hr : r != 0) :
    p ∣ r • X i ↔ exists s, s ∣ r ∧ (p = C s ∨ p = s • X i) := by
  rw [X]; rw [smul_monomial]; rw [smul_eq_mul]; rw [mul_one]; rw [dvd_monomial_iff_exists hr]; rw [exists_comm]
  apply exists_congr
  intro b
  constructor
  · rintro ⟨m, hmn, hb, rfl⟩
    simp only [hb, true_and]
    suffices m = 0 ∨ m = Finsupp.single i 1 by
      apply this.imp <;> simp +contextual [smul_monomial, smul_eq_mul, mul_one]
    by_cases hm : m i = 0
    · left
      ext j
      simp only [Finsupp.coe_zero, Pi.zero_apply, ← Nat.le_zero]
      by_cases hj : j = i
      · rw [← hm, hj]
      · exact (hmn j).trans (Finsupp.single_eq_of_ne hj).le
    · right
      ext j
      apply le_antisymm (hmn j)
      by_cases hj : j = i
      · simpa [hj, Nat.one_le_iff_ne_zero]
      · simp [Finsupp.single_eq_of_ne hj]
  · rintro ⟨hb, hp | hp⟩
    · use 0; simp [hb, hp]
    · use Finsupp.single i 1, le_rfl, hb
      simp [hp, smul_monomial]

/--
theorem `dvd_X_iff_exists` / 定理 `dvd_X_iff_exists`

English:
theorem dvd_X_iff_exists
  given: {i : σ}
  proof: by
  nontriviality R
  rw [← one_smul R (X i)]; rw [dvd_smul_X_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro r
  rw [isUnit_iff_dvd_one]; rw [one_smul]

中文:
定理 dvd_X_iff_存在
  条件: {i : σ}
  证明: by
  nontriviality R
  rw [← one_smul R (X i)]; rw [dvd_smul_X_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro r
  rw [isUnit_iff_dvd_one]; rw [one_smul]

Depends on / 依赖: dvd_smul_X_iff_exists, exists_congr, isUnit_iff_dvd_one, nontriviality, one_ne_zero, one_smul
-/
theorem dvd_X_iff_exists {i : σ} :
    p ∣ X i ↔ exists r, IsUnit r ∧ (p = C r ∨ p = r • X i) := by
  nontriviality R
  rw [← one_smul R (X i)]; rw [dvd_smul_X_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro r
  rw [isUnit_iff_dvd_one]; rw [one_smul]

end CommRing

end MvPolynomial
