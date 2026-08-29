/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Factors as finsupp

## Main definitions
* `UniqueFactorizationMonoid.factorization`: the multiset of irreducible factors as a `Finsupp`.
-/

@[expose] public section

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

section Finsupp

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
variable [NormalizationMonoid α] [DecidableEq α]

open UniqueFactorizationMonoid

/--
Definition of `factorization` / `factorization` 的定义

English:
definition factorization
  signature: (n : α)
  body: Multiset.toFinsupp (normalizedFactors n)

中文:
定义 factorization
  签名: (n : α)
  定义体: Multiset.toFinsupp (normalizedFactors n)

Depends on / 依赖: Multiset, Multiset.toFinsupp, normalizedFactors, toFinsupp
-/
noncomputable def factorization (n : α) : α ->₀ Nat :=
  Multiset.toFinsupp (normalizedFactors n)

/--
theorem `factorization_eq_count` / 定理 `factorization_eq_count`

English:
theorem factorization_eq_count
  given: {n p : α}
  proof: by simp [factorization]

@[simp]

中文:
定理 factorization_eq_count
  条件: {n p : α}
  证明: by simp [factorization]

@[simp]

Depends on / 依赖: factorization
-/
theorem factorization_eq_count {n p : α} :
    factorization n p = Multiset.count p (normalizedFactors n) := by simp [factorization]

@[simp]
/--
theorem `factorization_zero` / 定理 `factorization_zero`

English:
theorem factorization_zero
  statement: factorization (0 : α) = 0
  proof: by simp [factorization]

@[simp]

中文:
定理 factorization_zero
  结论: factorization (0 : α) = 0
  证明: by simp [factorization]

@[simp]

Depends on / 依赖: factorization
-/
theorem factorization_zero : factorization (0 : α) = 0 := by simp [factorization]

@[simp]
/--
theorem `factorization_one` / 定理 `factorization_one`

English:
theorem factorization_one
  statement: factorization (1 : α) = 0
  proof: by simp [factorization]

中文:
定理 factorization_one
  结论: factorization (1 : α) = 0
  证明: by simp [factorization]

Depends on / 依赖: factorization
-/
theorem factorization_one : factorization (1 : α) = 0 := by simp [factorization]

/-- The support of `factorization n` is exactly the Finset of normalized factors -/
@[simp]
/--
theorem `support_factorization` / 定理 `support_factorization`

English:
theorem support_factorization
  given: {n : α}
  proof: by
  simp [factorization, Multiset.toFinsupp_support]

中文:
定理 support_factorization
  条件: {n : α}
  证明: by
  simp [factorization, Multiset.toFinsupp_support]

Depends on / 依赖: Multiset, Multiset.toFinsupp_support, factorization, toFinsupp_support
-/
theorem support_factorization {n : α} :
    (factorization n).support = (normalizedFactors n).toFinset := by
  simp [factorization, Multiset.toFinsupp_support]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp]
/--
theorem `factorization_mul` / 定理 `factorization_mul`

English:
theorem factorization_mul
  given: {a b : α} (ha : a != 0) (hb : b != 0)
  proof: by
  simp [factorization, normalizedFactors_mul ha hb]

中文:
定理 factorization_mul
  条件: {a b : α} (ha : a != 0) (hb : b != 0)
  证明: by
  simp [factorization, normalizedFactors_mul ha hb]

Depends on / 依赖: factorization, normalizedFactors_mul
-/
theorem factorization_mul {a b : α} (ha : a != 0) (hb : b != 0) :
    factorization (a * b) = factorization a + factorization b := by
  simp [factorization, normalizedFactors_mul ha hb]

/--
theorem `factorization_pow` / 定理 `factorization_pow`

English:
theorem factorization_pow
  given: {x : α} {n : Nat}
  statement: factorization (x ^ n) = n • factorization x
  proof: by
  ext
  simp [factorization]

中文:
定理 factorization_pow
  条件: {x : α} {n : 自然数}
  结论: factorization (x ^ n) = n • factorization x
  证明: by
  ext
  simp [factorization]

Depends on / 依赖: factorization
-/
theorem factorization_pow {x : α} {n : Nat} : factorization (x ^ n) = n • factorization x := by
  ext
  simp [factorization]

/--
theorem `associated_of_factorization_eq` / 定理 `associated_of_factorization_eq`

English:
theorem associated_of_factorization_eq
  statement: (a b : α) (ha : a != 0) (hb : b != 0)
  proof: by
  simp_rw [factorization, AddEquiv.apply_eq_iff_eq] at h
  rwa [associated_iff_normalizedFactors_eq_normalizedFactors ha hb]

中文:
定理 associated_of_factorization_eq
  结论: (a b : α) (ha : a != 0) (hb : b != 0)
  证明: by
  simp_rw [factorization, AddEquiv.apply_eq_iff_eq] at h
  rwa [associated_iff_normalizedFactors_eq_normalizedFactors ha hb]

Depends on / 依赖: AddEquiv, AddEquiv.apply_eq_iff_eq, apply_eq_iff_eq, associated_iff_normalizedFactors_eq_normalizedFactors, factorization, simp_rw
-/
theorem associated_of_factorization_eq (a b : α) (ha : a != 0) (hb : b != 0)
    (h : factorization a = factorization b) : Associated a b := by
  simp_rw [factorization, AddEquiv.apply_eq_iff_eq] at h
  rwa [associated_iff_normalizedFactors_eq_normalizedFactors ha hb]

end Finsupp
