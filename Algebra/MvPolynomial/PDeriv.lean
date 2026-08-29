/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Yury Kudryashov
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `MvPolynomial.pderiv i p` : the partial derivative of `p` with respect to `i`, as a bundled
  derivation of `MvPolynomial σ R`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommRing R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/

@[expose] public section


noncomputable section

universe u v

namespace MvPolynomial

open Set Function Finsupp

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ ->₀ Nat}

section PDeriv

variable [CommSemiring R]

/--
Definition of `pderiv` / `pderiv` 的定义

English:
definition pderiv
  signature: (i : σ)
  body: letI := Classical.decEq σ
mkDerivation R Pi.single i 1

中文:
定义 pderiv
  签名: (i : σ)
  定义体: letI := Classical.decEq σ
mkDerivation R Pi.single i 1

Depends on / 依赖: Classical, Classical.decEq, Pi.single, mkDerivation, single
-/
def pderiv (i : σ) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  letI := Classical.decEq σ
mkDerivation R Pi.single i 1

/--
theorem `pderiv_def` / 定理 `pderiv_def`

English:
theorem pderiv_def
  given: [DecidableEq σ] (i : σ)
  statement: pderiv i = mkDerivation R (Pi.single i 1)
  proof: by
  unfold pderiv; congr!

@[simp]

中文:
定理 pderiv_def
  条件: [DecidableEq σ] (i : σ)
  结论: pderiv i = mkDerivation R (Pi.single i 1)
  证明: by
  unfold pderiv; congr!

@[simp]

Depends on / 依赖: pderiv
-/
theorem pderiv_def [DecidableEq σ] (i : σ) : pderiv i = mkDerivation R (Pi.single i 1) := by
  unfold pderiv; congr!

@[simp]
/--
theorem `pderiv_monomial` / 定理 `pderiv_monomial`

English:
theorem pderiv_monomial
  given: {i : σ}
  proof: by
  classical
  simp only [pderiv_def, mkDerivation_monomial, Finsupp.smul_sum, smul_eq_mul, ← smul_mul_assoc,
    ← (monomial _).map_smul]
  refine (Finset.sum_eq_single i (fun j _ hne => ?_) fun hi => ?_).trans ?_
  · simp [Pi.single_eq_of_ne hne]
  · rw [Finsupp.notMem_support_iff] at hi; simp [

中文:
定理 pderiv_monomial
  条件: {i : σ}
  证明: by
  classical
  simp only [pderiv_def, mkDerivation_monomial, Finsupp.smul_sum, smul_eq_mul, ← smul_mul_assoc,
    ← (monomial _).map_smul]
  refine (Finset.sum_eq_single i (fun j _ hne => ?_) fun hi => ?_).trans ?_
  · simp [Pi.single_eq_of_ne hne]
  · rw [Finsupp.notMem_support_iff] at hi; simp [

Depends on / 依赖: Finset, Finset.sum_eq_single, Finsupp, Finsupp.notMem_support_iff, Finsupp.smul_sum, Pi.single_eq_of_ne, classical, map_smul, mkDerivation_monomial, monomial, notMem_support_iff, pderiv_def, single_eq_of_ne, smul_eq_mul, smul_mul_assoc, smul_sum, sum_eq_single
-/
theorem pderiv_monomial {i : σ} :
    pderiv i (monomial s a) = monomial (s - single i 1) (a * s i) := by
  classical
  simp only [pderiv_def, mkDerivation_monomial, Finsupp.smul_sum, smul_eq_mul, ← smul_mul_assoc,
    ← (monomial _).map_smul]
  refine (Finset.sum_eq_single i (fun j _ hne => ?_) fun hi => ?_).trans ?_
  · simp [Pi.single_eq_of_ne hne]
  · rw [Finsupp.notMem_support_iff] at hi; simp [hi]
  · simp

/--
lemma `X_mul_pderiv_monomial` / 引理 `X_mul_pderiv_monomial`

English:
lemma X_mul_pderiv_monomial
  given: {i : σ} {m : σ ->₀ Nat} {r : R}
  proof: by
  rw [pderiv_monomial]; rw [X]; rw [monomial_mul]; rw [smul_monomial]
  by_cases h : m i = 0
  · simp_rw [h, Nat.cast_zero, mul_zero, zero_smul, monomial_zero]
  rw [one_mul]; rw [mul_comm]; rw [nsmul_eq_mul]; rw [add_comm]; rw [sub_add_single_one_cancel h]

中文:
引理 X_mul_pderiv_monomial
  条件: {i : σ} {m : σ ->₀ 自然数} {r : R}
  证明: by
  rw [pderiv_monomial]; rw [X]; rw [monomial_mul]; rw [smul_monomial]
  by_cases h : m i = 0
  · simp_rw [h, Nat.cast_zero, mul_zero, zero_smul, monomial_zero]
  rw [one_mul]; rw [mul_comm]; rw [nsmul_eq_mul]; rw [add_comm]; rw [sub_add_single_one_cancel h]

Depends on / 依赖: Nat.cast_zero, add_comm, cast_zero, monomial_mul, monomial_zero, mul_comm, mul_zero, nsmul_eq_mul, one_mul, pderiv_monomial, simp_rw, smul_monomial, sub_add_single_one_cancel, zero_smul
-/
lemma X_mul_pderiv_monomial {i : σ} {m : σ ->₀ Nat} {r : R} :
    X i * pderiv i (monomial m r) = m i • monomial m r := by
  rw [pderiv_monomial]; rw [X]; rw [monomial_mul]; rw [smul_monomial]
  by_cases h : m i = 0
  · simp_rw [h, Nat.cast_zero, mul_zero, zero_smul, monomial_zero]
  rw [one_mul]; rw [mul_comm]; rw [nsmul_eq_mul]; rw [add_comm]; rw [sub_add_single_one_cancel h]

/--
theorem `pderiv_C` / 定理 `pderiv_C`

English:
theorem pderiv_C
  given: {i : σ}
  statement: pderiv i (C a) = 0
  proof: derivation_C _ _

中文:
定理 pderiv_C
  条件: {i : σ}
  结论: pderiv i (C a) = 0
  证明: derivation_C _ _

Depends on / 依赖: derivation_C
-/
theorem pderiv_C {i : σ} : pderiv i (C a) = 0 :=
  derivation_C _ _

/--
theorem `pderiv_one` / 定理 `pderiv_one`

English:
theorem pderiv_one
  given: {i : σ}
  statement: pderiv i (1 : MvPolynomial σ R) = 0
  proof: pderiv_C

@[simp]

中文:
定理 pderiv_one
  条件: {i : σ}
  结论: pderiv i (1 : MvPolynomial σ R) = 0
  证明: pderiv_C

@[simp]

Depends on / 依赖: pderiv_C
-/
theorem pderiv_one {i : σ} : pderiv i (1 : MvPolynomial σ R) = 0 := pderiv_C

@[simp]
/--
theorem `pderiv_X` / 定理 `pderiv_X`

English:
theorem pderiv_X
  given: [DecidableEq σ] (i j : σ)
  proof: by
  rw [pderiv_def]; rw [mkDerivation_X]

@[simp]

中文:
定理 pderiv_X
  条件: [DecidableEq σ] (i j : σ)
  证明: by
  rw [pderiv_def]; rw [mkDerivation_X]

@[simp]

Depends on / 依赖: mkDerivation_X, pderiv_def
-/
theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv i (X j : MvPolynomial σ R) = Pi.single (M := fun _ => _) i 1 j := by
  rw [pderiv_def]; rw [mkDerivation_X]

@[simp]
/--
theorem `pderiv_X_self` / 定理 `pderiv_X_self`

English:
theorem pderiv_X_self
  given: (i : σ)
  statement: pderiv i (X i : MvPolynomial σ R) = 1
  proof: by classical simp

@[simp]

中文:
定理 pderiv_X_self
  条件: (i : σ)
  结论: pderiv i (X i : MvPolynomial σ R) = 1
  证明: by classical simp

@[simp]

Depends on / 依赖: classical
-/
theorem pderiv_X_self (i : σ) : pderiv i (X i : MvPolynomial σ R) = 1 := by classical simp

@[simp]
/--
theorem `pderiv_X_of_ne` / 定理 `pderiv_X_of_ne`

English:
theorem pderiv_X_of_ne
  given: {i j : σ} (h : j != i)
  statement: pderiv i (X j : MvPolynomial σ R) = 0
  proof: by
  classical simp [h]

中文:
定理 pderiv_X_of_ne
  条件: {i j : σ} (h : j != i)
  结论: pderiv i (X j : MvPolynomial σ R) = 0
  证明: by
  classical simp [h]

Depends on / 依赖: classical
-/
theorem pderiv_X_of_ne {i j : σ} (h : j != i) : pderiv i (X j : MvPolynomial σ R) = 0 := by
  classical simp [h]

/--
theorem `pderiv_eq_zero_of_notMem_vars` / 定理 `pderiv_eq_zero_of_notMem_vars`

English:
theorem pderiv_eq_zero_of_notMem_vars
  given: {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars)
  proof: derivation_eq_zero_of_forall_mem_vars fun _ hj => pderiv_X_of_ne ne_of_mem_of_not_mem hj h

中文:
定理 pderiv_eq_zero_of_notMem_vars
  条件: {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars)
  证明: derivation_eq_zero_of_forall_mem_vars fun _ hj => pderiv_X_of_ne ne_of_mem_of_not_mem hj h

Depends on / 依赖: derivation_eq_zero_of_forall_mem_vars, ne_of_mem_of_not_mem, pderiv_X_of_ne
-/
theorem pderiv_eq_zero_of_notMem_vars {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars) :
    pderiv i f = 0 :=
derivation_eq_zero_of_forall_mem_vars fun _ hj => pderiv_X_of_ne ne_of_mem_of_not_mem hj h

/--
theorem `pderiv_monomial_single` / 定理 `pderiv_monomial_single`

English:
theorem pderiv_monomial_single
  given: {i : σ} {n : Nat}
  statement: pderiv i (monomial (single i n) a) =
  proof: by simp

中文:
定理 pderiv_monomial_single
  条件: {i : σ} {n : 自然数}
  结论: pderiv i (monomial (single i n) a) =
  证明: by simp
-/
theorem pderiv_monomial_single {i : σ} {n : Nat} : pderiv i (monomial (single i n) a) =
    monomial (single i (n - 1)) (a * n) := by simp

/--
theorem `pderiv_mul` / 定理 `pderiv_mul`

English:
theorem pderiv_mul
  given: {i : σ} {f g : MvPolynomial σ R}
  proof: by
  simp only [(pderiv i).leibniz f g, smul_eq_mul, mul_comm, add_comm]

中文:
定理 pderiv_mul
  条件: {i : σ} {f g : MvPolynomial σ R}
  证明: by
  simp only [(pderiv i).leibniz f g, smul_eq_mul, mul_comm, add_comm]

Depends on / 依赖: add_comm, leibniz, mul_comm, pderiv, smul_eq_mul
-/
theorem pderiv_mul {i : σ} {f g : MvPolynomial σ R} :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  simp only [(pderiv i).leibniz f g, smul_eq_mul, mul_comm, add_comm]

/--
theorem `pderiv_pow` / 定理 `pderiv_pow`

English:
theorem pderiv_pow
  given: {i : σ} {f : MvPolynomial σ R} {n : Nat}
  proof: by
  rw [(pderiv i).leibniz_pow f n]; rw [nsmul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

中文:
定理 pderiv_pow
  条件: {i : σ} {f : MvPolynomial σ R} {n : 自然数}
  证明: by
  rw [(pderiv i).leibniz_pow f n]; rw [nsmul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

Depends on / 依赖: leibniz_pow, mul_assoc, nsmul_eq_mul, pderiv, smul_eq_mul
-/
theorem pderiv_pow {i : σ} {f : MvPolynomial σ R} {n : Nat} :
    pderiv i (f ^ n) = n * f ^ (n - 1) * pderiv i f := by
  rw [(pderiv i).leibniz_pow f n]; rw [nsmul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

/--
theorem `pderiv_C_mul` / 定理 `pderiv_C_mul`

English:
theorem pderiv_C_mul
  given: {f : MvPolynomial σ R} {i : σ}
  statement: pderiv i (C a * f) = C a * pderiv i f
  proof: by
  rw [C_mul']; rw [Derivation.map_smul]; rw [C_mul']

中文:
定理 pderiv_C_mul
  条件: {f : MvPolynomial σ R} {i : σ}
  结论: pderiv i (C a * f) = C a * pderiv i f
  证明: by
  rw [C_mul']; rw [Derivation.map_smul]; rw [C_mul']

Depends on / 依赖: C_mul, Derivation, Derivation.map_smul, map_smul
-/
theorem pderiv_C_mul {f : MvPolynomial σ R} {i : σ} : pderiv i (C a * f) = C a * pderiv i f := by
  rw [C_mul']; rw [Derivation.map_smul]; rw [C_mul']

/--
theorem `coeff_pderiv` / 定理 `coeff_pderiv`

English:
theorem coeff_pderiv
  given: {i : σ} (p : MvPolynomial σ R) (m : σ ->₀ Nat)
  proof: by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a =>
    rw [pderiv_monomial]; rw [coeff_monomial]; rw [coeff_monomial]
    by_cases h : n = m + single i 1
    · simp [h]
    simp only [h, ↓reduceIte, zero_mul]
    by_case

中文:
定理 coeff_pderiv
  条件: {i : σ} (p : MvPolynomial σ R) (m : σ ->₀ 自然数)
  证明: by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a =>
    rw [pderiv_monomial]; rw [coeff_monomial]; rw [coeff_monomial]
    by_cases h : n = m + single i 1
    · simp [h]
    simp only [h, ↓reduceIte, zero_mul]
    by_case

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, add_mul, classical, coeff_monomial, if_neg, induction_on, monomial, pderiv_monomial, reduceIte, single, tsub_eq_iff_eq_add_of_le, zero_mul
-/
theorem coeff_pderiv {i : σ} (p : MvPolynomial σ R) (m : σ ->₀ Nat) :
    coeff m (pderiv i p) = coeff (m + single i 1) p * (m i + 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a =>
    rw [pderiv_monomial]; rw [coeff_monomial]; rw [coeff_monomial]
    by_cases h : n = m + single i 1
    · simp [h]
    simp only [h, ↓reduceIte, zero_mul]
    by_cases hn : n i = 0
    · simp [hn]
    apply if_neg
    rwa [tsub_eq_iff_eq_add_of_le (fun _ => by grind)]

/--
theorem `pderiv_map` / 定理 `pderiv_map`

English:
theorem pderiv_map
  given: {S} [CommSemiring S] {φ : R ->+* S} {f : MvPolynomial σ R} {i : σ}
  proof: by
  apply induction_on f (fun r => by simp) (fun p q hp hq => by simp [hp, hq]) fun p j eq => ?_
  obtain rfl | h := eq_or_ne j i
  · simp [eq]
  · simp [eq, h]

中文:
定理 pderiv_map
  条件: {S} [CommSemiring S] {φ : R ->+* S} {f : MvPolynomial σ R} {i : σ}
  证明: by
  apply induction_on f (fun r => by simp) (fun p q hp hq => by simp [hp, hq]) fun p j eq => ?_
  obtain rfl | h := eq_or_ne j i
  · simp [eq]
  · simp [eq, h]

Depends on / 依赖: eq_or_ne, induction_on
-/
theorem pderiv_map {S} [CommSemiring S] {φ : R ->+* S} {f : MvPolynomial σ R} {i : σ} :
    pderiv i (map φ f) = map φ (pderiv i f) := by
  apply induction_on f (fun r => by simp) (fun p q hp hq => by simp [hp, hq]) fun p j eq => ?_
  obtain rfl | h := eq_or_ne j i
  · simp [eq]
  · simp [eq, h]

/--
lemma `pderiv_rename` / 引理 `pderiv_rename`

English:
lemma pderiv_rename
  statement: {τ : Type*} {f : σ -> τ} (hf : Function.Injective f)
  proof: by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a h =>
    simp only [map_mul, MvPolynomial.rename_X, Derivation.leibniz, MvPolynomial.pderiv_X,
      Pi.single_apply, hf.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero,

中文:
引理 pderiv_rename
  结论: {τ : 类型} {f : σ -> τ} (hf : Function.Injective f)
  证明: by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a h =>
    simp only [map_mul, MvPolynomial.rename_X, Derivation.leibniz, MvPolynomial.pderiv_X,
      Pi.single_apply, hf.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero,

Depends on / 依赖: Derivation, Derivation.leibniz, MvPolynomial, MvPolynomial.induction_on, MvPolynomial.pderiv_X, MvPolynomial.rename_X, Pi.single_apply, classical, eq_iff, hf.eq_iff, induction_on, leibniz, map_add, map_mul, mul_X, mul_ite, mul_one, mul_zero, pderiv_X, rename_X
-/
lemma pderiv_rename {τ : Type*} {f : σ -> τ} (hf : Function.Injective f)
    (x : σ) (p : MvPolynomial σ R) :
    pderiv (f x) (rename f p) = rename f (pderiv x p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a h =>
    simp only [map_mul, MvPolynomial.rename_X, Derivation.leibniz, MvPolynomial.pderiv_X,
      Pi.single_apply, hf.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero, h, map_add]
    split_ifs <;> simp

/--
lemma `aeval_sumElim_pderiv_inl` / 引理 `aeval_sumElim_pderiv_inl`

English:
lemma aeval_sumElim_pderiv_inl
  statement: {S τ : Type*} [CommRing S] [Algebra R S]
  proof: by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q h =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, h]
    cases q <;> simp [Pi.single_apply]

@[simp]

中文:
引理 aeval_sumElim_pderiv_inl
  结论: {S τ : 类型} [CommRing S] [Algebra R S]
  证明: by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q h =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, h]
    cases q <;> simp [Pi.single_apply]

@[simp]

Depends on / 依赖: Derivation, Derivation.leibniz, MvPolynomial, MvPolynomial.induction_on, Pi.single_apply, aeval_X, classical, induction_on, leibniz, map_add, map_mul, mul_X, pderiv_X, single_apply, smul_eq_mul
-/
lemma aeval_sumElim_pderiv_inl {S τ : Type*} [CommRing S] [Algebra R S]
    (p : MvPolynomial (σ oplus τ) R) (f : τ -> S) (j : σ) :
    aeval (Sum.elim X (C ∘ f)) ((pderiv (Sum.inl j)) p) =
      (pderiv j) ((aeval (Sum.elim X (C ∘ f))) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q h =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, h]
    cases q <;> simp [Pi.single_apply]

@[simp]
/--
lemma `pderiv_sumRingEquiv` / 引理 `pderiv_sumRingEquiv`

English:
lemma pderiv_sumRingEquiv
  given: {σ ι} (p i)
  proof: by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | mul_X p n _ => cases n <;> simp_all [pderiv_X, Pi.single_apply, apply_ite]

@[deprecated (since := "2026-06-18")] alias pderiv_sumToIter := pderiv_sumRingEquiv

@[simp]

中文:
引理 pderiv_sumRingEquiv
  条件: {σ ι} (p i)
  证明: by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | mul_X p n _ => cases n <;> simp_all [pderiv_X, Pi.single_apply, apply_ite]

@[deprecated (since := "2026-06-18")] alias pderiv_sumToIter := pderiv_sumRingEquiv

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, Pi.single_apply, apply_ite, classical, induction_on, mul_X, pderiv_X, single_apply
-/
lemma pderiv_sumRingEquiv {σ ι} (p i) :
    (sumRingEquiv R σ ι p).pderiv i = sumRingEquiv R σ ι (p.pderiv (.inl i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | mul_X p n _ => cases n <;> simp_all [pderiv_X, Pi.single_apply, apply_ite]

@[deprecated (since := "2026-06-18")] alias pderiv_sumToIter := pderiv_sumRingEquiv

@[simp]
/--
lemma `pderiv_sumAlgEquiv` / 引理 `pderiv_sumAlgEquiv`

English:
lemma pderiv_sumAlgEquiv
  statement: {R S₁ S₂ : Type*} [CommSemiring R]
  proof: pderiv_sumRingEquiv ..

中文:
引理 pderiv_sumAlgEquiv
  结论: {R S₁ S₂ : 类型} [CommSemiring R]
  证明: pderiv_sumRingEquiv ..

Depends on / 依赖: pderiv_sumRingEquiv
-/
lemma pderiv_sumAlgEquiv {R S₁ S₂ : Type*} [CommSemiring R]
    (b : S₁) (p : MvPolynomial (S₁ oplus S₂) R) :
    pderiv b (sumAlgEquiv R S₁ S₂ p) = sumAlgEquiv R S₁ S₂ (pderiv (Sum.inl b) p) :=
  pderiv_sumRingEquiv ..

end PDeriv

end MvPolynomial
