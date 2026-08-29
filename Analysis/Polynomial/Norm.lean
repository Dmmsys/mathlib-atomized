/-
Copyright (c) 2025 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.RingTheory.Polynomial.GaussNorm
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Algebra.Order.Hom.Basic


/-!
# Sup Norm of Polynomials

In this file we define the sup norm on `Polynomial`s based on their coefficients as well as several
basic results about this norm. We note that this is often called the _(naive) height_ of the
polynomial in the literature.

The sup norm is related to the Mahler measure of the polynomial. See
`Mathlib/Analysis/Polynomial/MahlerMeasure.lean`.

## Main definitions

- `Polynomial.supNorm p`: the sup norm of the coefficients of the polynomial, equal to the
  maximum of the norm of its coefficients (or zero for the zero polynomial)

## A Note on Naming

In the literature, the sup norm is often called the _(naive) height_ of a polynomial and the
`l^1` norm is often called the _length_ of the polynomial. Unfortunately, these terms are
extremely overloaded and Mathlib defines _height_ differently.

### TODOs

All other `l^p` norms can be defined on Polynomials as well. In the literature, the `l^1` norm is
sometimes called the polynomial's _length_. The `l^2` norm sometimes arises due to Parseval's
theorem implying that the squared `l^2` norm of a complex polynomial is the integral of the norm of
the polynomial's value on the unit circle.
-/


@[expose] public section supnorm_seminorm

variable {A : Type*} [SeminormedRing A] (p : Polynomial A)

namespace Polynomial

/--
Definition of `supNorm` / `supNorm` 的定义

English:
definition supNorm
  signature: : Real
  body: p.gaussNorm (SeminormedRing.toRingSeminorm A) 1

中文:
定义 supNorm
  签名: : 实数
  定义体: p.gaussNorm (SeminormedRing.toRingSeminorm A) 1

Depends on / 依赖: SeminormedRing, SeminormedRing.toRingSeminorm, gaussNorm, p.gaussNorm, toRingSeminorm
-/
noncomputable def supNorm : Real := p.gaussNorm (SeminormedRing.toRingSeminorm A) 1

/--
lemma `supNorm_def'` / 引理 `supNorm_def'`

English:
lemma supNorm_def'
  statement: p.supNorm =
  proof: by
  split_ifs with h
  · simp only [supNorm, gaussNorm, h, ↓reduceDIte, one_pow, mul_one, Function.comp_apply]
    congr
  · simp [supNorm, gaussNorm, h]

@[simp]

中文:
引理 supNorm_def'
  结论: p.supNorm =
  证明: by
  split_ifs with h
  · simp only [supNorm, gaussNorm, h, ↓reduceDIte, one_pow, mul_one, Function.comp_apply]
    congr
  · simp [supNorm, gaussNorm, h]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, gaussNorm, mul_one, one_pow, reduceDIte, split_ifs, supNorm
-/
lemma supNorm_def' : p.supNorm =
    if hp : p.support.Nonempty then p.support.sup' hp (norm ∘ p.coeff) else 0 := by
  split_ifs with h
  · simp only [supNorm, gaussNorm, h, ↓reduceDIte, one_pow, mul_one, Function.comp_apply]
    congr
  · simp [supNorm, gaussNorm, h]

@[simp]
/--
lemma `supNorm_zero` / 引理 `supNorm_zero`

English:
lemma supNorm_zero
  statement: (0 : A[X]).supNorm = 0
  proof: gaussNorm_zero ..

中文:
引理 supNorm_zero
  结论: (0 : A[X]).supNorm = 0
  证明: gaussNorm_zero ..

Depends on / 依赖: gaussNorm_zero
-/
lemma supNorm_zero : (0 : A[X]).supNorm = 0 := gaussNorm_zero ..

/--
lemma `supNorm_nonneg` / 引理 `supNorm_nonneg`

English:
lemma supNorm_nonneg
  statement: 0 <= p.supNorm
  proof: by
  apply gaussNorm_nonneg
  norm_num

@[simp]

中文:
引理 supNorm_nonneg
  结论: 0 <= p.supNorm
  证明: by
  apply gaussNorm_nonneg
  norm_num

@[simp]

Depends on / 依赖: gaussNorm_nonneg
-/
lemma supNorm_nonneg : 0 <= p.supNorm := by
  apply gaussNorm_nonneg
  norm_num

@[simp]
/--
lemma `supNorm_C` / 引理 `supNorm_C`

English:
lemma supNorm_C
  given: {a : A}
  statement: (C a).supNorm = ‖a‖
  proof: gaussNorm_C ..

@[simp]

中文:
引理 supNorm_C
  条件: {a : A}
  结论: (C a).supNorm = ‖a‖
  证明: gaussNorm_C ..

@[simp]

Depends on / 依赖: gaussNorm_C
-/
lemma supNorm_C {a : A} : (C a).supNorm = ‖a‖ := gaussNorm_C ..

@[simp]
/--
lemma `supNorm_monomial` / 引理 `supNorm_monomial`

English:
lemma supNorm_monomial
  given: (n : Nat) {a : A}
  statement: (monomial n a).supNorm = ‖a‖
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  · simp [supNorm, gaussNorm, support_monomial n ha]

@[simp]

中文:
引理 supNorm_monomial
  条件: (n : 自然数) {a : A}
  结论: (monomial n a).supNorm = ‖a‖
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  · simp [supNorm, gaussNorm, support_monomial n ha]

@[simp]

Depends on / 依赖: gaussNorm, supNorm, support_monomial
-/
lemma supNorm_monomial (n : Nat) {a : A} : (monomial n a).supNorm = ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [supNorm, gaussNorm, support_monomial n ha]

@[simp]
/--
lemma `supNorm_X` / 引理 `supNorm_X`

English:
lemma supNorm_X
  given: [NormOneClass A]
  statement: (X : A[X]).supNorm = 1
  proof: by
  rw [← monomial_one_one_eq_X]; rw [supNorm_monomial]; rw [norm_one]

中文:
引理 supNorm_X
  条件: [NormOneClass A]
  结论: (X : A[X]).supNorm = 1
  证明: by
  rw [← monomial_one_one_eq_X]; rw [supNorm_monomial]; rw [norm_one]

Depends on / 依赖: monomial_one_one_eq_X, norm_one, supNorm_monomial
-/
lemma supNorm_X [NormOneClass A] : (X : A[X]).supNorm = 1 := by
  rw [← monomial_one_one_eq_X]; rw [supNorm_monomial]; rw [norm_one]

/--
lemma `le_supNorm` / 引理 `le_supNorm`

English:
lemma le_supNorm
  given: (i : Nat)
  statement: ‖p.coeff i‖ <= p.supNorm
  proof: by
  simpa using! le_gaussNorm (SeminormedRing.toRingSeminorm A) p (by norm_num : (0 : Real) <= 1) i

中文:
引理 le_supNorm
  条件: (i : 自然数)
  结论: ‖p.coeff i‖ <= p.supNorm
  证明: by
  simpa using! le_gaussNorm (SeminormedRing.toRingSeminorm A) p (by norm_num : (0 : Real) <= 1) i

Depends on / 依赖: SeminormedRing, SeminormedRing.toRingSeminorm, le_gaussNorm, toRingSeminorm
-/
lemma le_supNorm (i : Nat) : ‖p.coeff i‖ <= p.supNorm := by
  simpa using! le_gaussNorm (SeminormedRing.toRingSeminorm A) p (by norm_num : (0 : Real) <= 1) i

/--
lemma `exists_eq_supNorm` / 引理 `exists_eq_supNorm`

English:
lemma exists_eq_supNorm
  statement: exists i : Nat, p.supNorm = ‖p.coeff i‖
  proof: by
  simpa using! p.exists_eq_gaussNorm (SeminormedRing.toRingSeminorm A) 1

中文:
引理 exists_eq_supNorm
  结论: 存在 i : 自然数, p.supNorm = ‖p.coeff i‖
  证明: by
  simpa using! p.exists_eq_gaussNorm (SeminormedRing.toRingSeminorm A) 1

Depends on / 依赖: SeminormedRing, SeminormedRing.toRingSeminorm, exists_eq_gaussNorm, p.exists_eq_gaussNorm, toRingSeminorm
-/
lemma exists_eq_supNorm : exists i : Nat, p.supNorm = ‖p.coeff i‖ := by
  simpa using! p.exists_eq_gaussNorm (SeminormedRing.toRingSeminorm A) 1

/--
lemma `isGreatest_supNorm` / 引理 `isGreatest_supNorm`

English:
lemma isGreatest_supNorm
  statement: IsGreatest (Set.range (‖p.coeff ·‖)) p.supNorm
  proof: ⟨by simpa [eq_comm] using exists_eq_supNorm p, by simpa [mem_upperBounds] using le_supNorm p⟩

中文:
引理 isGreatest_supNorm
  结论: IsGreatest (Set.range (‖p.coeff ·‖)) p.supNorm
  证明: ⟨by simpa [eq_comm] using exists_eq_supNorm p, by simpa [mem_upperBounds] using le_supNorm p⟩

Depends on / 依赖: eq_comm, exists_eq_supNorm, le_supNorm, mem_upperBounds
-/
lemma isGreatest_supNorm : IsGreatest (Set.range (‖p.coeff ·‖)) p.supNorm :=
  ⟨by simpa [eq_comm] using exists_eq_supNorm p, by simpa [mem_upperBounds] using le_supNorm p⟩

/--
lemma `supNorm_eq_iSup` / 引理 `supNorm_eq_iSup`

English:
lemma supNorm_eq_iSup
  statement: p.supNorm = ⨆ i, ‖p.coeff i‖
  proof: p.isGreatest_supNorm.csSup_eq.symm

中文:
引理 supNorm_eq_iSup
  结论: p.supNorm = ⨆ i, ‖p.coeff i‖
  证明: p.isGreatest_supNorm.csSup_eq.symm

Depends on / 依赖: csSup_eq, isGreatest_supNorm, p.isGreatest_supNorm.csSup_eq.symm
-/
lemma supNorm_eq_iSup : p.supNorm = ⨆ i, ‖p.coeff i‖ := p.isGreatest_supNorm.csSup_eq.symm

end Polynomial
end supnorm_seminorm

@[expose] public section supnorm_norm

namespace Polynomial

variable {A : Type*} [NormedRing A] (p : Polynomial A)

/--
lemma `supNorm_eq_zero_iff` / 引理 `supNorm_eq_zero_iff`

English:
lemma supNorm_eq_zero_iff
  statement: p.supNorm = 0 ↔ p = 0
  proof: gaussNorm_eq_zero_iff _ _ (by simp) (by simp)

中文:
引理 supNorm_eq_zero_iff
  结论: p.supNorm = 0 ↔ p = 0
  证明: gaussNorm_eq_zero_iff _ _ (by simp) (by simp)

Depends on / 依赖: gaussNorm_eq_zero_iff
-/
lemma supNorm_eq_zero_iff : p.supNorm = 0 ↔ p = 0 := gaussNorm_eq_zero_iff _ _ (by simp) (by simp)

end Polynomial

end supnorm_norm
