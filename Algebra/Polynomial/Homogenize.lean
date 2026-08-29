/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finsupp.Notation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogenize a univariate polynomial

In this file we define a function `Polynomial.homogenize p n`
that takes a polynomial `p` and a natural number `n`
and returns a homogeneous bivariate polynomial of degree `n`.

If `n` is at least the degree of `p`, then `(homogenize p n).eval ![x, 1] = p.eval x`.

We use `MvPolynomial (Fin 2) R` to represent bivariate polynomials
instead of `R[X][Y]` (i.e., `Polynomial (Polynomial R)`),
because Mathlib has a theory about homogeneous multivariate polynomials,
but not about homogeneous bivariate polynomials encoded as `R[X][Y]`.
-/

@[expose] public section

open Finset

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R]

/--
Definition of `homogenize` / `homogenize` 的定义

English:
definition homogenize
  signature: (p : R[X]) (n : Nat)
  body: ∑ kl in antidiagonal n, .monomial (fun₀ | 0 => kl.1 | 1 => kl.2) (p.coeff kl.1)

@[simp]

中文:
定义 homogenize
  签名: (p : R[X]) (n : 自然数)
  定义体: ∑ kl in antidiagonal n, .monomial (fun₀ | 0 => kl.1 | 1 => kl.2) (p.coeff kl.1)

@[simp]

Depends on / 依赖: antidiagonal, monomial, p.coeff
-/
noncomputable def homogenize (p : R[X]) (n : Nat) : MvPolynomial (Fin 2) R :=
  ∑ kl in antidiagonal n, .monomial (fun₀ | 0 => kl.1 | 1 => kl.2) (p.coeff kl.1)

@[simp]
/--
lemma `homogenize_zero` / 引理 `homogenize_zero`

English:
lemma homogenize_zero
  given: (n : Nat)
  statement: homogenize (0 : R[X]) n = 0
  proof: by
  simp [homogenize]

@[simp]

中文:
引理 homogenize_zero
  条件: (n : 自然数)
  结论: homogenize (0 : R[X]) n = 0
  证明: by
  simp [homogenize]

@[simp]

Depends on / 依赖: homogenize
-/
lemma homogenize_zero (n : Nat) : homogenize (0 : R[X]) n = 0 := by
  simp [homogenize]

@[simp]
/--
lemma `homogenize_add` / 引理 `homogenize_add`

English:
lemma homogenize_add
  given: (p q : R[X]) (n : Nat)
  proof: by
  simp [homogenize, Finset.sum_add_distrib]

@[simp]

中文:
引理 homogenize_add
  条件: (p q : R[X]) (n : 自然数)
  证明: by
  simp [homogenize, Finset.sum_add_distrib]

@[simp]

Depends on / 依赖: Finset, Finset.sum_add_distrib, homogenize, sum_add_distrib
-/
lemma homogenize_add (p q : R[X]) (n : Nat) :
    homogenize (p + q) n = homogenize p n + homogenize q n := by
  simp [homogenize, Finset.sum_add_distrib]

@[simp]
/--
lemma `homogenize_smul` / 引理 `homogenize_smul`

English:
lemma homogenize_smul
  given: {S : Type*} [Semiring S] [Module S R] (c : S) (p : R[X]) (n : Nat)
  proof: by
  simp [homogenize, Finset.smul_sum, MvPolynomial.smul_monomial]

中文:
引理 homogenize_smul
  条件: {S : 类型} [半环 S] [模 S R] (c : S) (p : R[X]) (n : 自然数)
  证明: by
  simp [homogenize, Finset.smul_sum, MvPolynomial.smul_monomial]

Depends on / 依赖: Finset, Finset.smul_sum, MvPolynomial, MvPolynomial.smul_monomial, homogenize, smul_monomial, smul_sum
-/
lemma homogenize_smul {S : Type*} [Semiring S] [Module S R] (c : S) (p : R[X]) (n : Nat) :
    homogenize (c • p) n = c • homogenize p n := by
  simp [homogenize, Finset.smul_sum, MvPolynomial.smul_monomial]

/-- `homogenize` as a bundled linear map. -/
@[simps]
/--
Definition of `homogenizeLM` / `homogenizeLM` 的定义

English:
definition homogenizeLM
  signature: (n : Nat)
  body: homogenize p n
  map_add' := (homogenize_add · · n)
  map_smul' := (homogenize_smul · · n)

@[simp]

中文:
定义 homogenizeLM
  签名: (n : 自然数)
  定义体: homogenize p n
  map_add' := (homogenize_add · · n)
  map_smul' := (homogenize_smul · · n)

@[simp]

Depends on / 依赖: homogenize
-/
noncomputable def homogenizeLM (n : Nat) : R[X] ->ₗ[R] MvPolynomial (Fin 2) R where
  toFun p := homogenize p n
  map_add' := (homogenize_add · · n)
  map_smul' := (homogenize_smul · · n)

@[simp]
/--
lemma `homogenize_finsetSum` / 引理 `homogenize_finsetSum`

English:
lemma homogenize_finsetSum
  given: {ι : Type*} (s : Finset ι) (p : ι -> R[X]) (n : Nat)
  proof: _root_.map_sum (homogenizeLM n) p s

中文:
引理 homogenize_finsetSum
  条件: {ι : 类型} (s : 有限集 ι) (p : ι -> R[X]) (n : 自然数)
  证明: _root_.map_sum (homogenizeLM n) p s

Depends on / 依赖: _root_, _root_.map_sum, homogenizeLM, map_sum
-/
lemma homogenize_finsetSum {ι : Type*} (s : Finset ι) (p : ι -> R[X]) (n : Nat) :
    homogenize (∑ i in s, p i) n = ∑ i in s, homogenize (p i) n :=
  _root_.map_sum (homogenizeLM n) p s

/--
lemma `homogenize_map` / 引理 `homogenize_map`

English:
lemma homogenize_map
  given: {S : Type*} [CommSemiring S] (f : R ->+* S) (p : R[X]) (n : Nat)
  proof: by
  simp [homogenize]

@[simp]

中文:
引理 homogenize_map
  条件: {S : 类型} [交换半环 S] (f : R ->+* S) (p : R[X]) (n : 自然数)
  证明: by
  simp [homogenize]

@[simp]

Depends on / 依赖: SMulCommClass, Submonoid, Submonoid.center, center, homogenize
-/
lemma homogenize_map {S : Type*} [CommSemiring S] (f : R ->+* S) (p : R[X]) (n : Nat) :
    homogenize (p.map f) n = MvPolynomial.map f (homogenize p n) := by
  simp [homogenize]

@[simp]
/--
lemma `homogenize_C_mul` / 引理 `homogenize_C_mul`

English:
lemma homogenize_C_mul
  given: (c : R) (p : R[X]) (n : Nat)
  proof: by
  simp only [C_mul', homogenize_smul, MvPolynomial.C_mul']

@[simp]

中文:
引理 homogenize_C_mul
  条件: (c : R) (p : R[X]) (n : 自然数)
  证明: by
  simp only [C_mul', homogenize_smul, MvPolynomial.C_mul']

@[simp]

Depends on / 依赖: C_mul, MvPolynomial, MvPolynomial.C_mul, SMulCommClass, Submonoid, Submonoid.center, center, homogenize_smul
-/
lemma homogenize_C_mul (c : R) (p : R[X]) (n : Nat) :
    homogenize (C c * p) n = .C c * homogenize p n := by
  simp only [C_mul', homogenize_smul, MvPolynomial.C_mul']

@[simp]
/--
lemma `homogenize_monomial` / 引理 `homogenize_monomial`

English:
lemma homogenize_monomial
  given: {m n : Nat} (h : m <= n) (r : R)
  proof: by
  rw [homogenize]; rw [Finset.sum_eq_single (a := (m]; rw [n - m))]
  · simp
  · aesop (add simp coeff_monomial)
  · simp [h]

中文:
引理 homogenize_monomial
  条件: {m n : 自然数} (h : m <= n) (r : R)
  证明: by
  rw [homogenize]; rw [Finset.sum_eq_single (a := (m]; rw [n - m))]
  · simp
  · aesop (add simp coeff_monomial)
  · simp [h]

Depends on / 依赖: Finset, Finset.sum_eq_single, coeff_monomial, homogenize, sum_eq_single
-/
lemma homogenize_monomial {m n : Nat} (h : m <= n) (r : R) :
    homogenize (monomial m r) n = .monomial (fun₀ | 0 => m | 1 => n - m) r := by
  rw [homogenize]; rw [Finset.sum_eq_single (a := (m]; rw [n - m))]
  · simp
  · aesop (add simp coeff_monomial)
  · simp [h]

/--
lemma `homogenize_monomial_of_lt` / 引理 `homogenize_monomial_of_lt`

English:
lemma homogenize_monomial_of_lt
  given: {m n : Nat} (h : n < m) (r : R)
  proof: by
  rw [homogenize]
  apply Finset.sum_eq_zero
  aesop (add simp coeff_monomial)

@[simp]

中文:
引理 homogenize_monomial_of_lt
  条件: {m n : 自然数} (h : n < m) (r : R)
  证明: by
  rw [homogenize]
  apply Finset.sum_eq_zero
  aesop (add simp coeff_monomial)

@[simp]

Depends on / 依赖: Finset, Finset.sum_eq_zero, coeff_monomial, homogenize, sum_eq_zero
-/
lemma homogenize_monomial_of_lt {m n : Nat} (h : n < m) (r : R) :
    homogenize (monomial m r) n = 0 := by
  rw [homogenize]
  apply Finset.sum_eq_zero
  aesop (add simp coeff_monomial)

@[simp]
/--
lemma `homogenize_X_pow` / 引理 `homogenize_X_pow`

English:
lemma homogenize_X_pow
  given: {m n : Nat} (h : m <= n)
  proof: by
  rw [X_pow_eq_monomial]; rw [homogenize_monomial h]; rw [Finsupp.update_eq_add_single (by simp)]; rw [MvPolynomial.monomial_single_add]; rw [← MvPolynomial.X_pow_eq_monomial]

@[simp]

中文:
引理 homogenize_X_pow
  条件: {m n : 自然数} (h : m <= n)
  证明: by
  rw [X_pow_eq_monomial]; rw [homogenize_monomial h]; rw [Finsupp.update_eq_add_single (by simp)]; rw [MvPolynomial.monomial_single_add]; rw [← MvPolynomial.X_pow_eq_monomial]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.update_eq_add_single, MvPolynomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_single_add, X_pow_eq_monomial, homogenize_monomial, monomial_single_add, update_eq_add_single
-/
lemma homogenize_X_pow {m n : Nat} (h : m <= n) :
    homogenize (X ^ m : R[X]) n = .X 0 ^ m * .X 1 ^ (n - m) := by
  rw [X_pow_eq_monomial]; rw [homogenize_monomial h]; rw [Finsupp.update_eq_add_single (by simp)]; rw [MvPolynomial.monomial_single_add]; rw [← MvPolynomial.X_pow_eq_monomial]

@[simp]
/--
lemma `homogenize_X` / 引理 `homogenize_X`

English:
lemma homogenize_X
  given: {n : Nat} (hn : n != 0)
  statement: homogenize (X : R[X]) n = .X 0 * .X 1 ^ (n - 1)
  proof: by
  rw [← pow_one X]; rw [homogenize_X_pow]; rw [pow_one]
  rwa [Nat.one_le_iff_ne_zero]

@[simp]

中文:
引理 homogenize_X
  条件: {n : 自然数} (hn : n != 0)
  结论: homogenize (X : R[X]) n = .X 0 * .X 1 ^ (n - 1)
  证明: by
  rw [← pow_one X]; rw [homogenize_X_pow]; rw [pow_one]
  rwa [Nat.one_le_iff_ne_zero]

@[simp]

Depends on / 依赖: Nat.one_le_iff_ne_zero, SetLike, SubsemiringClass, homogenize_X_pow, one_le_iff_ne_zero, pow_one
-/
lemma homogenize_X {n : Nat} (hn : n != 0) : homogenize (X : R[X]) n = .X 0 * .X 1 ^ (n - 1) := by
  rw [← pow_one X]; rw [homogenize_X_pow]; rw [pow_one]
  rwa [Nat.one_le_iff_ne_zero]

@[simp]
/--
lemma `homogenize_C` / 引理 `homogenize_C`

English:
lemma homogenize_C
  given: (c : R) (n : Nat)
  statement: homogenize (.C c) n = .C c * .X 1 ^ n
  proof: by
  simpa [MvPolynomial.C_mul_X_pow_eq_monomial] using homogenize_monomial (Nat.zero_le n) c

@[simp]

中文:
引理 homogenize_C
  条件: (c : R) (n : 自然数)
  结论: homogenize (.C c) n = .C c * .X 1 ^ n
  证明: by
  simpa [MvPolynomial.C_mul_X_pow_eq_monomial] using homogenize_monomial (Nat.zero_le n) c

@[simp]

Depends on / 依赖: C_mul_X_pow_eq_monomial, MvPolynomial, MvPolynomial.C_mul_X_pow_eq_monomial, Nat.zero_le, homogenize_monomial, zero_le
-/
lemma homogenize_C (c : R) (n : Nat) : homogenize (.C c) n = .C c * .X 1 ^ n := by
  simpa [MvPolynomial.C_mul_X_pow_eq_monomial] using homogenize_monomial (Nat.zero_le n) c

@[simp]
/--
lemma `homogenize_one` / 引理 `homogenize_one`

English:
lemma homogenize_one
  given: (n : Nat)
  statement: homogenize (1 : R[X]) n = .X 1 ^ n
  proof: by
  simpa using homogenize_C (1 : R) n

中文:
引理 homogenize_one
  条件: (n : 自然数)
  结论: homogenize (1 : R[X]) n = .X 1 ^ n
  证明: by
  simpa using homogenize_C (1 : R) n

Depends on / 依赖: homogenize_C
-/
lemma homogenize_one (n : Nat) : homogenize (1 : R[X]) n = .X 1 ^ n := by
  simpa using homogenize_C (1 : R) n

/--
lemma `coeff_homogenize` / 引理 `coeff_homogenize`

English:
lemma coeff_homogenize
  given: (p : R[X]) (n : Nat) (m : Fin 2 ->₀ Nat)
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp [*, ite_add_ite]
  | monomial k c =>
    rcases le_or_gt k n with hkn | hnk
    · rw [homogenize_monomial hkn, coeff_monomial, MvPolynomial.coeff_monomial]
      have : (fun₀ | 0 => m 0 | 1 => m 1) = m := by ext i; fin_cases i <;> simp
      aesop
    · aesop (add simp homogenize_monomial_of_lt) (add simp coeff_monomial)

中文:
引理 coeff_homogenize
  条件: (p : R[X]) (n : 自然数) (m : 有限集 2 ->₀ 自然数)
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp [*, ite_add_ite]
  | monomial k c =>
    rcases le_or_gt k n with hkn | hnk
    · rw [homogenize_monomial hkn, coeff_monomial, MvPolynomial.coeff_monomial]
      have : (fun₀ | 0 => m 0 | 1 => m 1) = m := by ext i; fin_cases i <;> simp
      aesop
    · aesop (add simp homogenize_monomial_of_lt) (add simp coeff_monomial)

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_monomial, Polynomial, Polynomial.induction_on, coeff_monomial, fin_cases, homogenize_monomial, homogenize_monomial_of_lt, induction_on, ite_add_ite, le_or_gt, monomial
-/
lemma coeff_homogenize (p : R[X]) (n : Nat) (m : Fin 2 ->₀ Nat) :
    (homogenize p n).coeff m = if m 0 + m 1 = n then coeff p (m 0) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp [*, ite_add_ite]
  | monomial k c =>
    rcases le_or_gt k n with hkn | hnk
    · rw [homogenize_monomial hkn, coeff_monomial, MvPolynomial.coeff_monomial]
      have : (fun₀ | 0 => m 0 | 1 => m 1) = m := by ext i; fin_cases i <;> simp
      aesop
    · aesop (add simp homogenize_monomial_of_lt) (add simp coeff_monomial)

/--
lemma `eq_zero_of_homogenize_eq_zero` / 引理 `eq_zero_of_homogenize_eq_zero`

English:
lemma eq_zero_of_homogenize_eq_zero
  statement: {p : R[X]} {n : Nat} (hn : p.natDegree <= n)
  proof: by
  ext i
  simp only [coeff_zero]
  rcases le_or_gt i p.natDegree with H | H
  · have : p.coeff i = (p.homogenize n).coeff fun₀ | 0 => i | 1 => n - i := by
      simp [coeff_homogenize, Nat.add_sub_of_le (H.trans hn)]
    simp [this, h]
  · exact coeff_eq_zero_of_natDegree_lt H

中文:
引理 eq_zero_of_homogenize_eq_zero
  结论: {p : R[X]} {n : 自然数} (hn : p.natDegree <= n)
  证明: by
  ext i
  simp only [coeff_zero]
  rcases le_or_gt i p.natDegree with H | H
  · have : p.coeff i = (p.homogenize n).coeff fun₀ | 0 => i | 1 => n - i := by
      simp [coeff_homogenize, Nat.add_sub_of_le (H.trans hn)]
    simp [this, h]
  · exact coeff_eq_zero_of_natDegree_lt H

Depends on / 依赖: H.trans, Nat.add_sub_of_le, add_sub_of_le, coeff_eq_zero_of_natDegree_lt, coeff_homogenize, coeff_zero, homogenize, le_or_gt, natDegree, p.coeff, p.homogenize, p.natDegree
-/
lemma eq_zero_of_homogenize_eq_zero {p : R[X]} {n : Nat} (hn : p.natDegree <= n)
    (h : p.homogenize n = 0) :
    p = 0 := by
  ext i
  simp only [coeff_zero]
  rcases le_or_gt i p.natDegree with H | H
  · have : p.coeff i = (p.homogenize n).coeff fun₀ | 0 => i | 1 => n - i := by
      simp [coeff_homogenize, Nat.add_sub_of_le (H.trans hn)]
    simp [this, h]
  · exact coeff_eq_zero_of_natDegree_lt H

/--
lemma `homogenize_eq_zero_iff` / 引理 `homogenize_eq_zero_iff`

English:
lemma homogenize_eq_zero_iff
  given: {p : R[X]} {n : Nat} (hn : p.natDegree <= n)
  proof: ⟨eq_zero_of_homogenize_eq_zero hn, by simp +contextual⟩

中文:
引理 homogenize_eq_zero_iff
  条件: {p : R[X]} {n : 自然数} (hn : p.natDegree <= n)
  证明: ⟨eq_zero_of_homogenize_eq_zero hn, by simp +contextual⟩

Depends on / 依赖: SetLike, SubsemiringClass, contextual, eq_zero_of_homogenize_eq_zero
-/
lemma homogenize_eq_zero_iff {p : R[X]} {n : Nat} (hn : p.natDegree <= n) :
    p.homogenize n = 0 ↔ p = 0 :=
  ⟨eq_zero_of_homogenize_eq_zero hn, by simp +contextual⟩

/--
lemma `eval₂_homogenize_of_eq_one` / 引理 `eval₂_homogenize_of_eq_one`

English:
lemma eval₂_homogenize_of_eq_one
  statement: {S : Type*} [CommSemiring S] {p : R[X]} {n : Nat}
  proof: by
  apply Polynomial.induction_with_natDegree_le
    (fun p => MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0)) (N := n)
  · simp
  · simp +contextual [hg]
  · simp +contextual
  · assumption

中文:
引理 eval₂_homogenize_of_eq_one
  结论: {S : 类型} [交换半环 S] {p : R[X]} {n : 自然数}
  证明: by
  apply Polynomial.induction_with_natDegree_le
    (fun p => MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0)) (N := n)
  · simp
  · simp +contextual [hg]
  · simp +contextual
  · assumption

Depends on / 依赖: MvPolynomial, MvPolynomial.eval, Polynomial, Polynomial.induction_with_natDegree_le, contextual, homogenize, induction_with_natDegree_le, p.eval, p.homogenize
-/
lemma eval₂_homogenize_of_eq_one {S : Type*} [CommSemiring S] {p : R[X]} {n : Nat}
    (hn : natDegree p <= n) (f : R ->+* S) (g : Fin 2 -> S) (hg : g 1 = 1) :
    MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0) := by
  apply Polynomial.induction_with_natDegree_le
    (fun p => MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0)) (N := n)
  · simp
  · simp +contextual [hg]
  · simp +contextual
  · assumption

/--
lemma `aeval_homogenize_of_eq_one` / 引理 `aeval_homogenize_of_eq_one`

English:
lemma aeval_homogenize_of_eq_one
  statement: {A : Type*} [CommSemiring A] [Algebra R A] {p : R[X]} {n : Nat}
  proof: by
  apply eval₂_homogenize_of_eq_one <;> assumption

中文:
引理 aeval_homogenize_of_eq_one
  结论: {A : 类型} [交换半环 A] [代数 R A] {p : R[X]} {n : 自然数}
  证明: by
  apply eval₂_homogenize_of_eq_one <;> assumption

Depends on / 依赖: AddCommMonoid, Module, SetLike
-/
lemma aeval_homogenize_of_eq_one {A : Type*} [CommSemiring A] [Algebra R A] {p : R[X]} {n : Nat}
    (hn : natDegree p <= n) (g : Fin 2 -> A) (hg : g 1 = 1) :
    MvPolynomial.aeval g (p.homogenize n) = aeval (g 0) p := by
  apply eval₂_homogenize_of_eq_one <;> assumption

/-- If `deg p ≤ n`, then `homogenize p n (x, 1) = p x`. -/
@[simp]
/--
lemma `aeval_homogenize_X_one` / 引理 `aeval_homogenize_X_one`

English:
lemma aeval_homogenize_X_one
  given: (p : R[X]) {n : Nat} (hn : natDegree p <= n)
  proof: by
  rw [aeval_homogenize_of_eq_one] <;> simp [*]

@[simp]

中文:
引理 aeval_homogenize_X_one
  条件: (p : R[X]) {n : 自然数} (hn : natDegree p <= n)
  证明: by
  rw [aeval_homogenize_of_eq_one] <;> simp [*]

@[simp]

Depends on / 依赖: aeval_homogenize_of_eq_one
-/
lemma aeval_homogenize_X_one (p : R[X]) {n : Nat} (hn : natDegree p <= n) :
    MvPolynomial.aeval ![X, 1] (p.homogenize n) = p := by
  rw [aeval_homogenize_of_eq_one] <;> simp [*]

@[simp]
/--
lemma `isHomogeneous_homogenize` / 引理 `isHomogeneous_homogenize`

English:
lemma isHomogeneous_homogenize
  given: {n : Nat} (p : R[X])
  statement: (p.homogenize n).IsHomogeneous n
  proof: by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
  simp only [Prod.forall, mem_antidiagonal]
  rintro a b rfl
  apply MvPolynomial.isHomogeneous_monomial
  simp [Finsupp.update_eq_add_single]

中文:
引理 isHomogeneous_homogenize
  条件: {n : 自然数} (p : R[X])
  结论: (p.homogenize n).IsHomogeneous n
  证明: by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
  simp only [Prod.forall, mem_antidiagonal]
  rintro a b rfl
  apply MvPolynomial.isHomogeneous_monomial
  simp [Finsupp.update_eq_add_single]

Depends on / 依赖: Finsupp, Finsupp.update_eq_add_single, IsHomogeneous, MvPolynomial, MvPolynomial.IsHomogeneous.sum, MvPolynomial.isHomogeneous_monomial, Prod.forall, isHomogeneous_monomial, mem_antidiagonal, update_eq_add_single
-/
lemma isHomogeneous_homogenize {n : Nat} (p : R[X]) : (p.homogenize n).IsHomogeneous n := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
  simp only [Prod.forall, mem_antidiagonal]
  rintro a b rfl
  apply MvPolynomial.isHomogeneous_monomial
  simp [Finsupp.update_eq_add_single]

/--
lemma `homogenize_eq_of_isHomogeneous` / 引理 `homogenize_eq_of_isHomogeneous`

English:
lemma homogenize_eq_of_isHomogeneous
  statement: {p : R[X]} {n : Nat} {q : MvPolynomial (Fin 2) R}
  proof: by
  subst p
  rw [q.as_sum]
  simp only [MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial, ← C_eq_algebraMap,
    homogenize_finsetSum, homogenize_C_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.monomial_eq]
  congr 1
obtain rfl : m.weight 1 = n := hq by simpa using hm
  simp [Finsupp.prod_fintype, Finsupp.weight_apply, Finsupp.sum_fintype, Fin.prod_univ_two,
    Fin.sum_univ_two]

中文:
引理 homogenize_eq_of_isHomogeneous
  结论: {p : R[X]} {n : 自然数} {q : 多元多项式 (有限集 2) R}
  证明: by
  subst p
  rw [q.as_sum]
  simp only [MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial, ← C_eq_algebraMap,
    homogenize_finsetSum, homogenize_C_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.monomial_eq]
  congr 1
obtain rfl : m.weight 1 = n := hq by simpa using hm
  simp [Finsupp.prod_fintype, Finsupp.weight_apply, Finsupp.sum_fintype, Fin.prod_univ_two,
    Fin.sum_univ_two]

Depends on / 依赖: C_eq_algebraMap, Fin.prod_univ_two, Fin.sum_univ_two, Finset, Finset.sum_congr, Finsupp, Finsupp.prod_fintype, Finsupp.sum_fintype, Finsupp.weight_apply, MvPolynomial, MvPolynomial.aeval_monomial, MvPolynomial.aeval_sum, MvPolynomial.monomial_eq, Submonoid, Submonoid.center.smulCommClass_left, aeval_monomial, aeval_sum, as_sum, center, homogenize_C_mul
-/
lemma homogenize_eq_of_isHomogeneous {p : R[X]} {n : Nat} {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous n) (hpq : MvPolynomial.aeval ![X, 1] q = p) :
    p.homogenize n = q := by
  subst p
  rw [q.as_sum]
  simp only [MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial, ← C_eq_algebraMap,
    homogenize_finsetSum, homogenize_C_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.monomial_eq]
  congr 1
obtain rfl : m.weight 1 = n := hq by simpa using hm
  simp [Finsupp.prod_fintype, Finsupp.weight_apply, Finsupp.sum_fintype, Fin.prod_univ_two,
    Fin.sum_univ_two]

/--
lemma `homogenize_mul` / 引理 `homogenize_mul`

English:
lemma homogenize_mul
  given: (p q : R[X]) {m n : Nat} (hm : natDegree p <= m) (hn : natDegree q <= n)
  proof: by
  apply homogenize_eq_of_isHomogeneous
  · apply_rules [MvPolynomial.IsHomogeneous.mul, isHomogeneous_homogenize]
  · simp [*]

中文:
引理 homogenize_mul
  条件: (p q : R[X]) {m n : 自然数} (hm : natDegree p <= m) (hn : natDegree q <= n)
  证明: by
  apply homogenize_eq_of_isHomogeneous
  · apply_rules [MvPolynomial.IsHomogeneous.mul, isHomogeneous_homogenize]
  · simp [*]

Depends on / 依赖: IsHomogeneous, MvPolynomial, MvPolynomial.IsHomogeneous.mul, Submonoid, Submonoid.center.smulCommClass_right, apply_rules, center, homogenize_eq_of_isHomogeneous, isHomogeneous_homogenize, smulCommClass_right
-/
lemma homogenize_mul (p q : R[X]) {m n : Nat} (hm : natDegree p <= m) (hn : natDegree q <= n) :
    homogenize (p * q) (m + n) = homogenize p m * homogenize q n := by
  apply homogenize_eq_of_isHomogeneous
  · apply_rules [MvPolynomial.IsHomogeneous.mul, isHomogeneous_homogenize]
  · simp [*]

/--
lemma `homogenize_finsetProd` / 引理 `homogenize_finsetProd`

English:
lemma homogenize_finsetProd
  statement: {ι : Type*} {s : Finset ι} {p : ι -> R[X]} {n : ι -> Nat}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ihs =>
    simp only [prod_cons, sum_cons, forall_mem_cons] at *
    rw [homogenize_mul _ _ h.1]; rw [ihs h.2]
    exact (natDegree_prod_le _ _).trans (sum_le_sum h.2)

中文:
引理 homogenize_finsetProd
  结论: {ι : 类型} {s : 有限集 ι} {p : ι -> R[X]} {n : ι -> 自然数}
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ihs =>
    simp only [prod_cons, sum_cons, forall_mem_cons] at *
    rw [homogenize_mul _ _ h.1]; rw [ihs h.2]
    exact (natDegree_prod_le _ _).trans (sum_le_sum h.2)

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction, forall_mem_cons, homogenize_mul, natDegree_prod_le, prod_cons, sum_cons, sum_le_sum
-/
lemma homogenize_finsetProd {ι : Type*} {s : Finset ι} {p : ι -> R[X]} {n : ι -> Nat}
    (h : forall i in s, (p i).natDegree <= n i) :
    homogenize (∏ i in s, p i) (∑ i in s, n i) = ∏ i in s, homogenize (p i) (n i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ihs =>
    simp only [prod_cons, sum_cons, forall_mem_cons] at *
    rw [homogenize_mul _ _ h.1]; rw [ihs h.2]
    exact (natDegree_prod_le _ _).trans (sum_le_sum h.2)

/--
lemma `homogenize_dvd` / 引理 `homogenize_dvd`

English:
lemma homogenize_dvd
  given: [NoZeroDivisors R] {p q : R[X]} (h : p ∣ q)
  proof: by
  rcases h with ⟨r, rfl⟩
  obtain rfl | rfl | ⟨hp₀, hr₀⟩ : p = 0 ∨ r = 0 ∨ p != 0 ∧ r != 0 := by tauto
  · simp
  · simp
  · rw [natDegree_mul hp₀ hr₀, homogenize_mul _ _ le_rfl le_rfl]
    apply dvd_mul_right

中文:
引理 homogenize_dvd
  条件: [无零因子 R] {p q : R[X]} (h : p ∣ q)
  证明: by
  rcases h with ⟨r, rfl⟩
  obtain rfl | rfl | ⟨hp₀, hr₀⟩ : p = 0 ∨ r = 0 ∨ p != 0 ∧ r != 0 := by tauto
  · simp
  · simp
  · rw [natDegree_mul hp₀ hr₀, homogenize_mul _ _ le_rfl le_rfl]
    apply dvd_mul_right

Depends on / 依赖: dvd_mul_right, homogenize_mul, le_rfl, natDegree_mul
-/
lemma homogenize_dvd [NoZeroDivisors R] {p q : R[X]} (h : p ∣ q) :
    homogenize p p.natDegree ∣ homogenize q q.natDegree := by
  rcases h with ⟨r, rfl⟩
  obtain rfl | rfl | ⟨hp₀, hr₀⟩ : p = 0 ∨ r = 0 ∨ p != 0 ∧ r != 0 := by tauto
  · simp
  · simp
  · rw [natDegree_mul hp₀ hr₀, homogenize_mul _ _ le_rfl le_rfl]
    apply dvd_mul_right

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

@[simp]
/--
lemma `homogenize_neg` / 引理 `homogenize_neg`

English:
lemma homogenize_neg
  given: (p : R[X]) (n : Nat)
  statement: (-p).homogenize n = -p.homogenize n
  proof: map_neg (homogenizeLM n) p

@[simp]

中文:
引理 homogenize_neg
  条件: (p : R[X]) (n : 自然数)
  结论: (-p).homogenize n = -p.homogenize n
  证明: map_neg (homogenizeLM n) p

@[simp]

Depends on / 依赖: homogenizeLM, map_neg
-/
lemma homogenize_neg (p : R[X]) (n : Nat) : (-p).homogenize n = -p.homogenize n :=
  map_neg (homogenizeLM n) p

@[simp]
/--
lemma `homogenize_sub` / 引理 `homogenize_sub`

English:
lemma homogenize_sub
  given: (p q : R[X]) (n : Nat)
  proof: map_sub (homogenizeLM n) p q

中文:
引理 homogenize_sub
  条件: (p q : R[X]) (n : 自然数)
  证明: map_sub (homogenizeLM n) p q

Depends on / 依赖: homogenizeLM, map_sub
-/
lemma homogenize_sub (p q : R[X]) (n : Nat) :
    (p - q).homogenize n = p.homogenize n - q.homogenize n :=
  map_sub (homogenizeLM n) p q

end CommRing

section Semifield

variable {K : Type*} [Semifield K]

/--
lemma `eval_homogenize` / 引理 `eval_homogenize`

English:
lemma eval_homogenize
  given: {p : K[X]} {n : Nat} (hn : p.natDegree <= n) (x : Fin 2 -> K) (hx : x 1 != 0)
  proof: by
  simp only [homogenize, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hn),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [MvPolynomial.eval_monomial]; rw [Finsupp.update_eq_add_single]; rw [Finsupp.prod_add_index']; rw [Finsupp.prod_single_index]; rw [Finsupp.prod_single_index]; rw [pow_sub₀]
  · ring
  all_goals simp_all [pow_add]

中文:
引理 eval_homogenize
  条件: {p : K[X]} {n : 自然数} (hn : p.natDegree <= n) (x : 有限集 2 -> K) (hx : x 1 != 0)
  证明: by
  simp only [homogenize, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hn),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [MvPolynomial.eval_monomial]; rw [Finsupp.update_eq_add_single]; rw [Finsupp.prod_add_index']; rw [Finsupp.prod_single_index]; rw [Finsupp.prod_single_index]; rw [pow_sub₀]
  · ring
  all_goals simp_all [pow_add]

Depends on / 依赖: Finset, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_congr, Finset.sum_mul, Finsupp, Finsupp.prod_add_index, Finsupp.prod_single_index, Finsupp.update_eq_add_single, MvPolynomial, MvPolynomial.eval_monomial, MvPolynomial.eval_sum, Nat.lt_succ_iff.mpr, Polynomial, Polynomial.eval_eq_sum_range, all_goals, eval_eq_sum_range, eval_monomial, eval_sum, homogenize, lt_succ_iff
-/
lemma eval_homogenize {p : K[X]} {n : Nat} (hn : p.natDegree <= n) (x : Fin 2 -> K) (hx : x 1 != 0) :
    MvPolynomial.eval x (p.homogenize n) = p.eval (x 0 / x 1) * x 1 ^ n := by
  simp only [homogenize, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hn),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [MvPolynomial.eval_monomial]; rw [Finsupp.update_eq_add_single]; rw [Finsupp.prod_add_index']; rw [Finsupp.prod_single_index]; rw [Finsupp.prod_single_index]; rw [pow_sub₀]
  · ring
  all_goals simp_all [pow_add]

end Semifield

section projectivize

variable {R : Type*} [CommSemiring R]

/-- Given a polynomial `p : R[X]`, this is the vector `![p₀, p₁]` of homogeneous bivariate
polynomials of degree `p.natDegree` such that `p(x) = p₀(x,1)/p₁(x,1)` and `p₁` is a monomial. -/
noncomputable
/--
Definition of `toTupleMvPolynomial` / `toTupleMvPolynomial` 的定义

English:
definition toTupleMvPolynomial
  signature: (p : R[X])
  body: ![p.homogenize p.natDegree, (MvPolynomial.X 1) ^ p.natDegree]

中文:
定义 toTupleMvPolynomial
  签名: (p : R[X])
  定义体: ![p.homogenize p.natDegree, (MvPolynomial.X 1) ^ p.natDegree]

Depends on / 依赖: MvPolynomial, MvPolynomial.X, homogenize, natDegree, p.homogenize, p.natDegree
-/
def toTupleMvPolynomial (p : R[X]) : Fin 2 -> MvPolynomial (Fin 2) R :=
  ![p.homogenize p.natDegree, (MvPolynomial.X 1) ^ p.natDegree]

/--
lemma `toTupleMvPolynomial_zero_eq` / 引理 `toTupleMvPolynomial_zero_eq`

English:
lemma toTupleMvPolynomial_zero_eq
  given: (p : R[X])
  proof: rfl

中文:
引理 toTupleMvPolynomial_zero_eq
  条件: (p : R[X])
  证明: rfl
-/
lemma toTupleMvPolynomial_zero_eq (p : R[X]) :
    p.toTupleMvPolynomial 0 = p.homogenize p.natDegree :=
  rfl

/--
lemma `toTupleMvPolynomial_one_eq` / 引理 `toTupleMvPolynomial_one_eq`

English:
lemma toTupleMvPolynomial_one_eq
  given: (p : R[X])
  proof: rfl

中文:
引理 toTupleMvPolynomial_one_eq
  条件: (p : R[X])
  证明: rfl
-/
lemma toTupleMvPolynomial_one_eq (p : R[X]) :
    p.toTupleMvPolynomial 1 = (MvPolynomial.X 1) ^ p.natDegree :=
  rfl

/--
lemma `isHomogeneous_toTupleMvPolynomial` / 引理 `isHomogeneous_toTupleMvPolynomial`

English:
lemma isHomogeneous_toTupleMvPolynomial
  given: (p : R[X]) (i : Fin 2)
  proof: by
  fin_cases i
  · simp [toTupleMvPolynomial]
  · simpa [toTupleMvPolynomial] using MvPolynomial.isHomogeneous_X_pow 1 p.natDegree

@[deprecated (since := "2026-04-06")]
alias isHomogenous_toTupleMvPolynomial := isHomogeneous_toTupleMvPolynomial

中文:
引理 isHomogeneous_toTupleMvPolynomial
  条件: (p : R[X]) (i : 有限集 2)
  证明: by
  fin_cases i
  · simp [toTupleMvPolynomial]
  · simpa [toTupleMvPolynomial] using MvPolynomial.isHomogeneous_X_pow 1 p.natDegree

@[deprecated (since := "2026-04-06")]
alias isHomogenous_toTupleMvPolynomial := isHomogeneous_toTupleMvPolynomial

Depends on / 依赖: MvPolynomial, MvPolynomial.isHomogeneous_X_pow, fin_cases, isHomogeneous_X_pow, natDegree, p.natDegree, toTupleMvPolynomial
-/
lemma isHomogeneous_toTupleMvPolynomial (p : R[X]) (i : Fin 2) :
    (p.toTupleMvPolynomial i).IsHomogeneous p.natDegree := by
  fin_cases i
  · simp [toTupleMvPolynomial]
  · simpa [toTupleMvPolynomial] using MvPolynomial.isHomogeneous_X_pow 1 p.natDegree

@[deprecated (since := "2026-04-06")]
alias isHomogenous_toTupleMvPolynomial := isHomogeneous_toTupleMvPolynomial

/--
lemma `eval_X_toTupleMvPolynomial_zero_eq` / 引理 `eval_X_toTupleMvPolynomial_zero_eq`

English:
lemma eval_X_toTupleMvPolynomial_zero_eq
  given: (p : R[X])
  proof: by
  simp [toTupleMvPolynomial]

中文:
引理 eval_X_toTupleMvPolynomial_zero_eq
  条件: (p : R[X])
  证明: by
  simp [toTupleMvPolynomial]

Depends on / 依赖: toTupleMvPolynomial
-/
lemma eval_X_toTupleMvPolynomial_zero_eq (p : R[X]) :
    MvPolynomial.aeval ![X, 1] (p.toTupleMvPolynomial 0) =
      p * MvPolynomial.aeval ![X, 1] (p.toTupleMvPolynomial 1) := by
  simp [toTupleMvPolynomial]

/--
lemma `eval_eq_div_eval_toTupleMvPolynomial` / 引理 `eval_eq_div_eval_toTupleMvPolynomial`

English:
lemma eval_eq_div_eval_toTupleMvPolynomial
  given: {R : Type*} [Field R] (p : R[X]) (x : R)
  proof: by
  simp [toTupleMvPolynomial, eval_homogenize]

中文:
引理 eval_eq_div_eval_toTupleMvPolynomial
  条件: {R : 类型} [域 R] (p : R[X]) (x : R)
  证明: by
  simp [toTupleMvPolynomial, eval_homogenize]

Depends on / 依赖: AddSubmonoidWithOneClass, AddSubmonoidWithOneClass.toAddMonoidWithOne, eval_homogenize, toAddMonoidWithOne, toTupleMvPolynomial
-/
lemma eval_eq_div_eval_toTupleMvPolynomial {R : Type*} [Field R] (p : R[X]) (x : R) :
    p.eval x =
      (p.toTupleMvPolynomial 0).eval ![x, 1] / (p.toTupleMvPolynomial 1).eval ![x, 1] := by
  simp [toTupleMvPolynomial, eval_homogenize]

/--
lemma `sum_eq_natDegree_of_mem_support_homogenize` / 引理 `sum_eq_natDegree_of_mem_support_homogenize`

English:
lemma sum_eq_natDegree_of_mem_support_homogenize
  statement: (p : R[X]) {s : Fin 2 ->₀ Nat}
  proof: by
  simp [(isHomogeneous_homogenize p).degree_eq_sum_deg_support hs, ← Finsupp.degree_apply,
        Finsupp.degree_eq_sum]

中文:
引理 sum_eq_natDegree_of_mem_support_homogenize
  结论: (p : R[X]) {s : 有限集 2 ->₀ 自然数}
  证明: by
  simp [(isHomogeneous_homogenize p).degree_eq_sum_deg_support hs, ← Finsupp.degree_apply,
        Finsupp.degree_eq_sum]

Depends on / 依赖: Finsupp, Finsupp.degree_apply, Finsupp.degree_eq_sum, SubsemiringClass, SubsemiringClass.addSubmonoidWithOneClass, addSubmonoidWithOneClass, degree_apply, degree_eq_sum, degree_eq_sum_deg_support, isHomogeneous_homogenize
-/
lemma sum_eq_natDegree_of_mem_support_homogenize (p : R[X]) {s : Fin 2 ->₀ Nat}
    (hs : s in (p.homogenize p.natDegree).support) :
    s 0 + s 1 = p.natDegree := by
  simp [(isHomogeneous_homogenize p).degree_eq_sum_deg_support hs, ← Finsupp.degree_apply,
        Finsupp.degree_eq_sum]

/--
lemma `finsuppSum_homogenize_eq` / 引理 `finsuppSum_homogenize_eq`

English:
lemma finsuppSum_homogenize_eq
  given: {M : Type*} [AddCommMonoid M] (p : R[X]) {f : R -> M}
  proof: by
  rw [MvPolynomial.sum_def]; rw [sum_def p]
  -- We set up a bijection between the sets indexing the terms on both sides
  -- and show that it maps the terms in the one sum to those in the other.
  refine Finset.sum_nbij' (fun s => s 0) (fun n => fun₀ | 0 => n | 1 => p.natDegree - n)
    (fun s hs => ?_) (fun n hn => ?_) (fun s hs => ?_) (fun n hn => by simp)
    fun s hs => ?_
  · simpa [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs] using hs
  · simpa [coeff_homogenize, mem_support_iff.mp hn]
using Nat.add_sub_of_le le_natDegree_of_mem_supp n hn
  · -- speeds up `grind` quite a bit
    grind only [= Finsupp.update_apply, = Finsupp.single_apply,
      sum_eq_natDegree_of_mem_support_homogenize p hs]
  · simp [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs]

中文:
引理 finsuppSum_homogenize_eq
  条件: {M : 类型} [加法交换幺半群 M] (p : R[X]) {f : R -> M}
  证明: by
  rw [MvPolynomial.sum_def]; rw [sum_def p]
  -- We set up a bijection between the sets indexing the terms on both sides
  -- and show that it maps the terms in the one sum to those in the other.
  refine Finset.sum_nbij' (fun s => s 0) (fun n => fun₀ | 0 => n | 1 => p.natDegree - n)
    (fun s hs => ?_) (fun n hn => ?_) (fun s hs => ?_) (fun n hn => by simp)
    fun s hs => ?_
  · simpa [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs] using hs
  · simpa [coeff_homogenize, mem_support_iff.mp hn]
using Nat.add_sub_of_le le_natDegree_of_mem_supp n hn
  · -- speeds up `grind` quite a bit
    grind only [= Finsupp.update_apply, = Finsupp.single_apply,
      sum_eq_natDegree_of_mem_support_homogenize p hs]
  · simp [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs]

Depends on / 依赖: MvPolynomial, MvPolynomial.sum_def, SubsemiringClass, SubsemiringClass.nonUnitalSubsemiringClass, nonUnitalSubsemiringClass, sum_def
-/
lemma finsuppSum_homogenize_eq {M : Type*} [AddCommMonoid M] (p : R[X]) {f : R -> M} :
    (AddMonoidAlgebra.coeff <| p.homogenize p.natDegree).sum (fun _ c => f c) =
      p.sum fun _ c => f c := by
  rw [MvPolynomial.sum_def]; rw [sum_def p]
  -- We set up a bijection between the sets indexing the terms on both sides
  -- and show that it maps the terms in the one sum to those in the other.
  refine Finset.sum_nbij' (fun s => s 0) (fun n => fun₀ | 0 => n | 1 => p.natDegree - n)
    (fun s hs => ?_) (fun n hn => ?_) (fun s hs => ?_) (fun n hn => by simp)
    fun s hs => ?_
  · simpa [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs] using hs
  · simpa [coeff_homogenize, mem_support_iff.mp hn]
using Nat.add_sub_of_le le_natDegree_of_mem_supp n hn
  · -- speeds up `grind` quite a bit
    grind only [= Finsupp.update_apply, = Finsupp.single_apply,
      sum_eq_natDegree_of_mem_support_homogenize p hs]
  · simp [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs]

end projectivize

end Polynomial
